(*
 * TODO: Fix functions stablecoins from m base coins and base coins for n stable
 * coins to incorporate volume of the current beta decay reaction in the beta
 * decay fee. Will need to modify correctness proofs as well.
 * TODO: Fix fusion function so that neutrons and protons are combined in the 
 * required ratio
 *)
(*
 * Importing the Libraries
 *)
From StableCoinFormalization Require Export Datatypes.
From StableCoinFormalization Require Export HelperFunctions.
Require Export Lra.

Local Open Scope R_scope.

Module Functions.
    Import Datatypes.
    Import HelperFunctions.
    Import Bool.
    Import Lra.
    Import Lia.

    (*
     * Defining Parameters
     *)
    
    Parameter qStar : QStar.
    Parameter fissionFee : FissionFee.
    Parameter fusionFee : FusionFee.
    Parameter betaDecayFee0 : BetaDecayFee0.
    Parameter betaDecayFee1 : BetaDecayFee1.
    Parameter timePeriod : TimePeriod.

    Axiom betaDecayFee_assumption :
        let betaDecayFee0Val := extract_value (betaDecayFee0) in
        let betaDecayFee1Val := extract_value (betaDecayFee1) in
        (0 < betaDecayFee0Val + betaDecayFee1Val <= 1).

    Axiom state_assumption :
        forall (s : State),
            (s.(stableCoinState).(reactorState).(baseCoins)) > 0 /\
            (s.(stableCoinState).(reactorState).(reserveCoins)) > 0 /\
            (s.(stableCoinState).(reactorState).(stableCoins)) > 0 /\
            (s.(stableCoinState).(exchangeRate)) > 0.
    
    Axiom reactorstate_assumption :
        forall (b : BaseCoins) (r : ReserveCoins) (s : StableCoins),
            b > 0 /\
            r > 0 /\
            s > 0.
    
    Axiom exchangerate_assumption :
        forall (e : ExchangeRate),
            e > 0.

    Axiom basecoin_assumption :
        forall (b : BaseCoins),
            b > 0.
    Axiom reservecoin_assumption :
        forall (r : ReserveCoins),
            r > 0.
    Axiom stablecoin_assumption :
        forall (s : StableCoins),
            s > 0.
    

    (*
     * Defining Functions
     *)

    Definition target_price 
        (state : StableCoinState) : BaseCoins :=

        state.(exchangeRate).

    Definition fusion_ratio 
        (state : StableCoinState) : R :=

        let baseCoinsVal := get_basecoins (state.(reactorState)) in
        let stableCoinsVal := get_stablecoins (state.(reactorState)) in
        let qStarVal := extract_value (qStar) in
        let exchangeRateVal := get_exchange_rate (state) in
        let otherValue := (stableCoinsVal * exchangeRateVal) / baseCoinsVal in 
        Rmin (qStarVal) (otherValue).
    
    Definition stablecoin_price 
        (state : StableCoinState) : R :=

        let fusionRatio := fusion_ratio (state) in
        let baseCoinsVal := get_basecoins (state.(reactorState)) in
        let stableCoinsVal := get_stablecoins (state.(reactorState)) in
        (fusionRatio * baseCoinsVal) / stableCoinsVal.

    Definition reservecoin_price 
        (state : StableCoinState) : R :=

        let fusionRatio := fusion_ratio (state) in
        let baseCoinsVal := get_basecoins (state.(reactorState)) in
        let reserveCoinsVal := get_reservecoins (state.(reactorState)) in
        (1 - fusionRatio) * baseCoinsVal / reserveCoinsVal. 
    
    Definition liabilities 
        (state : StableCoinState) : R :=

        let fusionRatio := fusion_ratio (state) in
        let baseCoinsVal := get_basecoins (state.(reactorState)) in
        fusionRatio * baseCoinsVal.
    
    Definition reserve_ratio 
        (state : StableCoinState) : R :=

        let fusionRatio := fusion_ratio (state) in
        1 / fusionRatio.
    
    Definition equity 
        (state : StableCoinState) : R :=

        let fusionRatio := fusion_ratio (state) in
        let baseCoinsVal := get_basecoins (state.(reactorState)) in
        (1 - fusionRatio) * baseCoinsVal.
    
    (*
     * Gets reactions with timestamp in the range 
     * lastTimestamp - timePeriod <= t <= lastTimestamp
     *)
    Definition reactions_slice 
        (reactions : Trace) 
        (lastTimestamp : nat) : Trace :=
        filter (
            fun x =>
                match x with
                | (_, t, _) => 
                    ((lastTimestamp - timePeriod) <=? t)
                    && (t <=? lastTimestamp)
                end
        ) reactions.

    Definition beta_pos_reactions 
        (reactions : Trace) 
        (lastTimestamp : nat) : Trace :=

        let slice := reactions_slice (reactions) (lastTimestamp) in
        filter (fun x => match x with
                        | (_, _, BetaDecayPosEvent _) => true
                        | _ => false
                        end) slice.
    
    Definition beta_neg_reactions 
        (reactions : Trace) 
        (lastTimestamp : nat) : Trace :=

        let slice := reactions_slice (reactions) (lastTimestamp) in
        filter (fun x => match x with
                        | (_, _, BetaDecayNegEvent _) => true
                        | _ => false
                        end) slice.
    
    Definition volume_beta_pos_reactions 
        (reactions : Trace) 
        (lastTimestamp : nat) : R :=

        let betaPosReactions := beta_pos_reactions (reactions) (lastTimestamp) in
        fold_right (fun x acc => match x with
                                | (stableCoinState, _, BetaDecayPosEvent reserveCoins) =>  
                                    (acc) + 
                                    (reserveCoins * 
                                    (reservecoin_price (stableCoinState)))
                                | _ => acc
                                end) 0 betaPosReactions.

    Definition volume_beta_neg_reactions 
        (reactions : Trace) 
        (lastTimestamp : nat) : R :=

        let betaNegReactions := beta_neg_reactions (reactions) (lastTimestamp) in
        fold_right (fun x acc => match x with
                                | (stableCoinState, _, BetaDecayNegEvent stableCoins) => 
                                    (acc) + 
                                    (stableCoins * 
                                    (stablecoin_price (stableCoinState)))
                                | _ => acc
                                end) 0 betaNegReactions.
    Fixpoint net_volume_before
        (reactions : Trace) 
        (lastTimestamp : nat) : R :=

        match reactions with
        | nil => 0
        | (sCS, t, e) :: reactions' =>
            if ((lastTimestamp - timePeriod) <=? t) && (t <=? lastTimestamp) 
            then
                match e with
                | BetaDecayPosEvent reserveCoins =>
                    let volume := reserveCoins * reservecoin_price (sCS) in
                    volume + net_volume_before (reactions') (lastTimestamp)
                | BetaDecayNegEvent stableCoins =>
                    let volume := stableCoins * stablecoin_price (sCS) in
                    (-volume) + net_volume_before (reactions') (lastTimestamp)
                | _ => net_volume_before (reactions') (lastTimestamp)
                end
            else
                0
        end.
                                
    Definition net_volume 
        (decay_event : Event)
        (reactions : Trace) 
        (stableCoinState : StableCoinState)
        (lastTimestamp : nat) : R :=

        match decay_event with
        | BetaDecayPosEvent reserveCoins =>
            let volume := reserveCoins * reservecoin_price (stableCoinState) in
            volume + net_volume_before (reactions) (lastTimestamp)
        | BetaDecayNegEvent stableCoins => 
            let volume := stableCoins * stablecoin_price (stableCoinState) in
            (-volume) + net_volume_before (reactions) (lastTimestamp)
        | _ => 0
        end.

    Definition beta_decay_pos_fee
        (decay_event : Event)
        (reactions : Trace)
        (stableCoinState : StableCoinState)
        (lastTimestamp : nat) : R :=

        let betaDecayFee0Val := extract_value (betaDecayFee0) in
        let betaDecayFee1Val := extract_value (betaDecayFee1) in
        let netVolume := net_volume (decay_event) (reactions) (stableCoinState) (lastTimestamp) in
        let totalBaseCoins := 
            get_basecoins (stableCoinState.(reactorState)) in
        (betaDecayFee0Val) +  
        ((betaDecayFee1Val) *  
         ((Rmax (netVolume) (0)) / totalBaseCoins)).
    
    Definition beta_decay_neg_fee 
        (decay_event : Event)
        (reactions : Trace)
        (stableCoinState : StableCoinState)
        (lastTimestamp : nat) : R :=

        let betaDecayFee0Val := extract_value (betaDecayFee0) in
        let betaDecayFee1Val := extract_value (betaDecayFee1) in
        let netVolume := net_volume (decay_event) (reactions) (stableCoinState) (lastTimestamp) in
        let totalBaseCoins := 
            get_basecoins (stableCoinState.(reactorState)) in
        (betaDecayFee0Val) +
        ((betaDecayFee1Val) * 
         ((Rmax (netVolume * -1) (0)) / (totalBaseCoins))).
    
    Definition fission_output 
        (baseCoins : BaseCoins) 
        (state : StableCoinState) : (R * R) :=
        let stableCoinsCirculation := 
            get_stablecoins (state.(reactorState)) in
        let reserveCoinsCirculation := 
            get_reservecoins (state.(reactorState)) in
        let baseCoinsContract := 
            get_basecoins (state.(reactorState)) in
        let reserveCoins := 
            (baseCoins * (1 - fusion_ratio (state)) * (1 - extract_value (fissionFee))) / (reservecoin_price (state)) in
        let stableCoins :=
            (baseCoins * fusion_ratio (state) * (1 - extract_value (fissionFee))) / (stablecoin_price (state)) in 
        (stableCoins, reserveCoins).

    Definition fission_reaction
        (stableCoinState : StableCoinState) 
        (baseCoins : BaseCoins) : StableCoinState :=
        let (stableCoins, reserveCoins) := fission_output (baseCoins) 
                                            (stableCoinState) in
        let oldReactorState := stableCoinState.(reactorState) in
        let newReactorState := Build_ReactorState 
                                (get_basecoins (oldReactorState) + baseCoins)
                                (get_stablecoins (oldReactorState) + stableCoins)
                                (get_reservecoins (oldReactorState) + reserveCoins) 
                                in
        Build_StableCoinState 
            (newReactorState) (get_exchange_rate (stableCoinState)).

    (*
     * This has the same signature as fission_output since users specify the 
     * of base coins they want and the required number of protons and neutrons
     * are deducted from their wallets.
     *)
    Definition fusion_output 
        (baseCoins : BaseCoins) 
        (state : StableCoinState) : (R * R) :=
        let stableCoinsCirculation := 
            get_stablecoins (state.(reactorState)) in
        let reserveCoinsCirculation :=
            get_reservecoins (state.(reactorState)) in
        let baseCoinsContract := 
            get_basecoins (state.(reactorState)) in
        let stableCoinsRequired := 
            (baseCoins * stableCoinsCirculation) / baseCoinsContract in
        let reserveCoinsRequired :=
            (baseCoins * reserveCoinsCirculation) / baseCoinsContract in
        (stableCoinsRequired, reserveCoinsRequired).
    

    Definition fusion_reaction
        (stableCoinState : StableCoinState) 
        (baseCoins : BaseCoins) : StableCoinState :=
        let baseCoinsContract := get_basecoins (stableCoinState.(reactorState)) in
        let (stableCoins, reserveCoins) := fusion_output (baseCoins) (stableCoinState) in
        let oldReactorState := stableCoinState.(reactorState) in
        let newReactorState := Build_ReactorState 
                                (get_basecoins (oldReactorState) - (baseCoins * (1 - extract_value (fusionFee))))
                                (get_stablecoins (oldReactorState) - stableCoins)
                                (get_reservecoins (oldReactorState) - reserveCoins) 
                                in
        Build_StableCoinState 
            (newReactorState) (get_exchange_rate (stableCoinState)).
        
    
    Definition beta_decay_pos_output 
        (reserveCoins : ReserveCoins) 
        (beta_decay_pos_fee : R) 
        (state : StableCoinState) : R :=
        (reserveCoins * (1 - beta_decay_pos_fee) * (reservecoin_price (state))) / stablecoin_price (state).
    
    Definition beta_decay_pos_reaction
        (stableCoinState : StableCoinState) 
        (beta_decay_pos_fee : R)
        (reserveCoins : ReserveCoins) : StableCoinState :=
        let reserveCoinsContract := get_reservecoins (stableCoinState.(reactorState)) in
        let stableCoins := beta_decay_pos_output
                        (reserveCoins) (beta_decay_pos_fee) (stableCoinState) in
        let oldReactorState := stableCoinState.(reactorState) in
        let newReactorState := Build_ReactorState 
                                (get_basecoins (oldReactorState))
                                (get_stablecoins (oldReactorState) + stableCoins)
                                (get_reservecoins (oldReactorState) - reserveCoins) 
                                in
        Build_StableCoinState 
            (newReactorState) (get_exchange_rate (stableCoinState)).

    Definition beta_decay_neg_output 
        (stableCoins : StableCoins) 
        (beta_decay_neg_fee : R) 
        (state : StableCoinState) : R :=
        (stableCoins * (1 - beta_decay_neg_fee) * (stablecoin_price (state))) / reservecoin_price (state).
        
    
    Definition beta_decay_neg_reaction
        (stableCoinState : StableCoinState) 
        (beta_decay_neg_fee : R)
        (stableCoins : StableCoins) : StableCoinState :=
        let stableCoinsContract := get_stablecoins (stableCoinState.(reactorState)) in
        let reserveCoins := beta_decay_neg_output
                        (stableCoins) (beta_decay_neg_fee) (stableCoinState) in
        let oldReactorState := stableCoinState.(reactorState) in
        let newReactorState := Build_ReactorState 
                                (get_basecoins (oldReactorState))
                                (get_stablecoins (oldReactorState) - stableCoins)
                                (get_reservecoins (oldReactorState) + reserveCoins) 
                                in
        Build_StableCoinState 
            (newReactorState) (get_exchange_rate (stableCoinState)).

    (*
     * This function executes the reaction and returns the new state
     * after executing the reaction.
     *)
    
    Definition execute (s : State) (e : Event) (t : Timestamp) : State :=
        let oldSCS := s.(stableCoinState) in
        let oldT := s.(reactions) in
        match e with
        | FissionEvent (bC) => 
            let newSCS := fission_reaction (oldSCS) (bC) in
            let newT := (oldSCS, t, e) :: oldT in
            Build_State (newSCS) (newT)
        | FusionEvent (bC) =>
            if Rlt_dec (bC) (get_basecoins (s.(stableCoinState).(reactorState))) 
            then
                let newSCS := fusion_reaction (oldSCS) (bC) in
                let newT := (oldSCS, t, e) :: oldT in
                Build_State (newSCS) (newT)
            else
                s
        (* 
         * Current Reaction also added to the oldT to take into account the 
         * volume of the current transaction 
         *)
        | BetaDecayPosEvent (rC) =>
            if Rlt_dec (rC) (get_reservecoins (s.(stableCoinState).(reactorState))) 
            then
                let fee := beta_decay_pos_fee (e) (s.(reactions)) (s.(stableCoinState)) (t) in
                let newSCS := beta_decay_pos_reaction (oldSCS) (fee) (rC) in
                let newT := (oldSCS, t, e) :: oldT in
                Build_State (newSCS) (newT)
            else
                s
        (* 
         * Current Reaction also added to the oldT to take into account the 
         * volume of the current transaction 
         *)
        | BetaDecayNegEvent (sC) =>
            if Rlt_dec (sC) (get_stablecoins (s.(stableCoinState).(reactorState))) 
            then
                let fee := beta_decay_neg_fee (e) (s.(reactions)) (s.(stableCoinState)) (t) in
                let newSCS := beta_decay_neg_reaction (oldSCS) (fee) (sC) in
                let newT := (oldSCS, t, e) :: oldT in
                Build_State (newSCS) (newT)
            else
                s
        end.

    
    (*
     * Theorem related functions
     *)
    
    (*
     * This function gives us the stablecoins we get from 'm' basecoins
     * state_0: stablecoin state before fission
     * timestamp: time when the beta decay + is initiated
     * state_1: stablecoin state before beta decay +
     * fracProtonsDecay: fraction of reserve coins from fission that are 
     *                   converted to stablecoins
     *)
    
    Definition stablecoins_from_m_basecoins
        (state_0 : State)
        (timestamp : nat)
        (state_1 : State)
        (baseCoins : R) 
        (betaDecayPosFeeVal : R)
        (fracProtonsDecay : R) : R :=
    let (stableCoins, reserveCoins) := fission_output (baseCoins) (state_0.(stableCoinState)) in
    let betaDecayFeePos := beta_decay_pos_fee (BetaDecayPosEvent (reserveCoins)) (state_1.(reactions)) (state_1.(stableCoinState)) (timestamp) in
    let stablecoinsFromDecay := beta_decay_pos_output (reserveCoins * fracProtonsDecay) (betaDecayPosFeeVal) (state_1.(stableCoinState)) in
    stableCoins + stablecoinsFromDecay.
    
    (*
     * This functions gives us the number of base coins we have to use for 
     * fission in order to get N stablecoins.
     * state_0: stablecoin state before fission
     * timestamp: time when the beta decay + is initiated
     * state_1: stablecoin state before beta decay +
     * fracProtonsDecay: fraction of reserve coins from fission that are 
     *                   converted to stablecoins
     * betaDecayPosFeeVal: the beta decay positive fee value. Will be in the
     *                         range (0, 1]                                     
     *)

    Definition base_coins_for_n_stable_coins
        (state_0 : State)
        (timestamp : nat)
        (state_1 : State)
        (stablecoinsRequired : R) 
        (betaDecayPosFeeVal : R)
        (fracProtonsDecay : R) : R :=
    let rInit := reservecoin_price (state_0.(stableCoinState)) in
    let rNew := reservecoin_price (state_1.(stableCoinState)) in
    let sInit := stablecoin_price (state_0.(stableCoinState)) in
    let sNew := stablecoin_price (state_1.(stableCoinState)) in
    let fInit := fusion_ratio (state_0.(stableCoinState)) in
    let fissionFeeVal := extract_value (fissionFee) in
    (rInit * sNew * sInit * stablecoinsRequired) / 
    ((fInit * (1 - fissionFeeVal) * rInit * sNew) + 
    ((1 - fInit) * fracProtonsDecay * (1 - fissionFeeVal) * (1 - betaDecayPosFeeVal) * rNew * sInit)).
    

    (*
     * This function returns the base coins we get when converting 'n' 
     * stablecoins into base coins where 'gamma' is the fraction of the 
     * stablecoins we convert to reserve coins for the fusion reaction after the
     * beta decay negative reaction.
     * state_0: state before beta decay negative reaction
     * timestamp: time when the beta decay negative reaction is initiated
     * gamma: fraction of stablecoins that are converted to reserve coins
     * stablecoins: stablecoins to be converted to base coins
     *)

    Definition base_coins_from_n_stable_coins
        (state_0 : State)
        (stable_coins : R)
        (gamma : R) : R :=
    let fusionFeeVal := extract_value (fusionFee) in
    let stablecoinPriceVal := stablecoin_price (state_0.(stableCoinState)) in
    let fusionRatioVal := fusion_ratio (state_0.(stableCoinState)) in
    let stableCoinsCurrent := get_stablecoins (state_0.(stableCoinState).(reactorState)) in
    ((1 - fusionFeeVal) * (1 - gamma) * stable_coins * stablecoinPriceVal)
    / 
    (fusionRatioVal * (1 - ((gamma * stable_coins) / (stableCoinsCurrent)))).

    
    (*
     * This function returns the effective fee in terms of base coins for the
     * action of selling/buying a stablecoin
     * TODO: Make effective fee functions separate for buying and selling 
     * stablecoins
     *)
    Definition get_effective_fee
        (timestamp : nat)
        (state_0 : State) 
        (state_1 : State)
        (gamma : R)
        (beta_decay_fee_val : R)
        (action : Action) : R :=
    match action with
    | SellStableCoin => 
        let baseCoinsFromOneStableCoin := base_coins_from_n_stable_coins (state_0) (1) (gamma) in
        let stableCoinPriceBeforeBetaDecay := stablecoin_price (state_0.(stableCoinState)) in
        1 - ((baseCoinsFromOneStableCoin) / (stableCoinPriceBeforeBetaDecay))
    | BuyStableCoin =>
        let baseCoinsForOneStableCoin := base_coins_for_n_stable_coins (state_0) (timestamp) (state_1) (1) (beta_decay_fee_val) (1) in
        let stableCoinPriceBeforeFission := stablecoin_price (state_0.(stableCoinState)) in
        (baseCoinsForOneStableCoin / stableCoinPriceBeforeFission) - 1
    end.
    
    (*
     * This function returns the price of buying/selling a stablecoin in terms
     * of base coins
     * TODO: Make this function separate for buying and selling stablecoins
     *)
    Definition get_primary_market_offer
        (timestamp : nat)
        (state_0 : State) 
        (state_1 : State)
        (gamma : R) 
        (betaDecayFeeVal : R) 
        (action : Action) : R :=
    match action with
    | BuyStableCoin => 
        (1 + get_effective_fee 
            (timestamp) (state_0) (state_1) (gamma) (betaDecayFeeVal) (action)) *
        (stablecoin_price (state_0.(stableCoinState)))
    | SellStableCoin =>  
        (1 - get_effective_fee 
            (timestamp) (state_0) (state_1) (gamma) (betaDecayFeeVal) (action)) *
        (stablecoin_price (state_0.(stableCoinState)))
    end.


    (*
     * This function returns the rational offer for a user.
     * For buying the user will pick the cheapest option and for selling
     * the stablecoin the user will pick the more expensive one. In case, the 
     * primary market offer and secondary market offer have the same value the
     * user defaults to the primary market.
     *)
    Definition get_rational_choice 
        (action : Action) 
        (primaryMarketOffer : R) 
        (secondaryMarketOffer : R) : Choice :=
    match action with
    | BuyStableCoin =>
        if Rlt_dec secondaryMarketOffer primaryMarketOffer
        then Secondary
        else Primary
    | SellStableCoin =>
        if Rgt_dec secondaryMarketOffer primaryMarketOffer
        then Secondary
        else Primary
    end.
    
    (*
     * This function returns a proposition that states: Trace of state_0 is a 
     * subset of trace of state_1
     *)
    Definition happened_after
        (state_0 : State)
        (state_1 : State) : Prop :=
    state_0.(reactions) = 
    firstn (length (state_0.(reactions))) (state_1.(reactions)).
        
    (*
     * This function checks if the stable coin state after executing a reaction
     * is the same as the previous stable coin state of the next reaction. 
     * reaction: latest reaction at the head of the list
     *)
    Fixpoint states_follow
        (reactions : Trace) : Prop :=
    match reactions with
    | nil => True
    | (s_2, t_2, r_2) :: reactions' =>
        match reactions' with
        | nil => True
        | (s_1, t_1, e_1) :: reactions'' =>
            match e_1 with
            | FissionEvent (baseCoins) => 
                (s_2 = fission_reaction (s_1) (baseCoins)) /\ 
                states_follow (reactions')
            | FusionEvent (baseCoins) =>
                (s_2 = fusion_reaction (s_1) (baseCoins)) /\ 
                states_follow (reactions')
            | BetaDecayPosEvent (reserveCoins) =>
                let beta_decay_pos_fee_val := 
                beta_decay_pos_fee (e_1) (reactions'') (s_1) (t_1) in
                (s_2 = beta_decay_pos_reaction (s_1) (beta_decay_pos_fee_val) (reserveCoins)) /\
                states_follow (reactions')
            | BetaDecayNegEvent (stableCoins) =>
                let beta_decay_neg_fee_val := 
                beta_decay_neg_fee (e_1) (reactions'') (s_1) (t_1) in
                (s_2 = beta_decay_neg_reaction (s_1) (beta_decay_neg_fee_val) (stableCoins)) /\
                states_follow (reactions')
            end
        end
    end.

    Fixpoint timestamps_increase 
        (reactions : Trace) : Prop :=
        match reactions with
        | nil => True
        | (_, t_2, _) :: reactions' =>
            match reactions' with
            | nil => True
            | (_, t_1, _) :: reactions'' =>
                (t_1 < t_2)%nat /\ timestamps_increase (reactions')
            end
        end.
    
    Definition curr_state_agrees_with_prev_state
        (state : State) : Prop :=
        let currStableCoinState := state.(stableCoinState) in
        let reactions := state.(reactions) in
            match reactions with
            | nil => True
            | (s, t, e) :: reactions' =>
                match e with
                | FissionEvent (baseCoins) => 
                    currStableCoinState = fission_reaction (s) (baseCoins)
                | FusionEvent (baseCoins) => 
                    currStableCoinState = 
                    fusion_reaction (s) (baseCoins)
                | BetaDecayPosEvent (reserveCoins) =>
                    let beta_decay_pos_fee_val := 
                    beta_decay_pos_fee (e) (reactions') (s) (t) in
                    currStableCoinState = 
                    beta_decay_pos_reaction 
                    (s) (beta_decay_pos_fee_val) (reserveCoins)
                | BetaDecayNegEvent (stableCoins) =>
                    let beta_decay_neg_fee_val := 
                    beta_decay_neg_fee (e) (reactions') (s) (t) in
                    currStableCoinState = 
                    beta_decay_neg_reaction 
                    (s) (beta_decay_neg_fee_val) (stableCoins)
                end
            end.


    (* 
     * (s1, t1, r1) , (s2, t2, r2)
     * This returns the proposition that a state is valid
     * Conditions to check:
     * 1. The stablecoin state after executing a reaction is the same as the 
     *    the stablecoin state prior to the next reaction that happened
     * 2. The timestamps increase starting from first reaction to the last one
     * 3. The stablecoin state after executing the last reaction is the same as
     *    the stablecoin state of the current 'state'
     *)
    Definition is_valid_state
        (state : State) : Prop :=
        states_follow (state.(reactions)) /\
        timestamps_increase (state.(reactions)) /\
        curr_state_agrees_with_prev_state (state).

    (*
     * Given 2 states s1, s2, this function calculates the base coin price crash
     * given by ((y - y') / y) where y, y' is the price of the base coin
     * (in terms of the pegged currency) before and after the crash respectively
     *)
    
    Definition base_coin_price_crash (s1 : State) (s2 : State) : R :=
        let price_before_crash := 1 / target_price (s1.(stableCoinState)) in
        let price_after_crash := 1 / target_price (s2.(stableCoinState)) in
            (price_before_crash - price_after_crash) / price_before_crash.
            
End Functions. 












