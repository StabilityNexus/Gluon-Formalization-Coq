(*
 * Importing the Libraries
 *)
From StableCoinFormalization Require Export Datatypes.
From StableCoinFormalization Require Export HelperFunctions.

Local Open Scope R_scope.

Module Functions.
    Import Datatypes.
    Import HelperFunctions.
    Import Bool.

    (*
     * Defining Parameters
     *)
    
    Parameter qStar : QStar.
    Parameter fissionFee : FissionFee.
    Parameter fusionFee : FusionFee.
    (*
     * TODO: Fix these to 0 and 1 or Rename to slope and intercept
     *)
    Parameter betaDecayFeePos : BetaDecayFeePos.
    Parameter betaDecayFeeNeg : BetaDecayFeeNeg.
    Parameter timePeriod : TimePeriod.

    Axiom betaDecayFee_assumption :
        let betaDecayFeePosVal := extract_value (betaDecayFeePos) in
        let betaDecayFeeNegVal := extract_value (betaDecayFeeNeg) in
        (0 < betaDecayFeePosVal + betaDecayFeeNegVal <= 1).
    
    Axiom reactorstate_assumption :
        forall (b : BaseCoins) (r : ReserveCoins) (s : StableCoins),
            b > 0 /\
            r > 0 /\
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
     * The reaction stored at the head of the trace has timestamp equal to the 
     * length of the trace. The reaction stored at the very end has timestamp 1.
     * elemsToSkip will equal 0 if lastTimestamp > totalLength.
     * firstn elemsToSelect slice will return the whole slice if 
     * elemsToSelect > length (slice)
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
                        | (_, _, BetaDecayPos _ _) => true
                        | _ => false
                        end) slice.
    
    Definition beta_neg_reactions 
        (reactions : Trace) 
        (lastTimestamp : nat) : Trace :=

        let slice := reactions_slice (reactions) (lastTimestamp) in
        filter (fun x => match x with
                        | (_, _, BetaDecayNeg _ _) => true
                        | _ => false
                        end) slice.
    
    Definition volume_beta_pos_reactions 
        (reactions : Trace) 
        (lastTimestamp : nat) : R :=

        let betaPosReactions := beta_pos_reactions (reactions) (lastTimestamp) in
        fold_right (fun x acc => match x with
                                | (stableCoinState, _, BetaDecayPos reserveCoins _) =>  
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
                                | (stableCoinState, _, BetaDecayNeg stableCoins _) => 
                                    (acc) + 
                                    (stableCoins * 
                                    (stablecoin_price (stableCoinState)))
                                | _ => acc
                                end) 0 betaNegReactions.
                                
    Definition net_volume 
        (reactions : Trace) 
        (lastTimestamp : nat) : R :=

        let betaPosVolume := 
            volume_beta_pos_reactions (reactions) (lastTimestamp) in
        let betaNegVolume := 
            volume_beta_neg_reactions (reactions) (lastTimestamp) in
        betaPosVolume - betaNegVolume.
    
    Definition beta_decay_pos_fee  
        (reactions : Trace)
        (stableCoinState : StableCoinState) 
        (lastTimestamp : nat) : R :=

        let betaDecayFeePosVal := extract_value (betaDecayFeePos) in
        let betaDecayFeeNegVal := extract_value (betaDecayFeeNeg) in
        let netVolume := net_volume (reactions) (lastTimestamp) in
        let totalBaseCoins := 
            get_basecoins (stableCoinState.(reactorState)) in
        (betaDecayFeePosVal) +  
        ((betaDecayFeeNegVal) *  
         ((Rmax (netVolume) (0)) / totalBaseCoins)).
    
    Definition beta_decay_neg_fee 
        (reactions : Trace)
        (stableCoinState : StableCoinState) 
        (lastTimestamp : nat) : R :=

        let betaDecayFeePosVal := extract_value (betaDecayFeePos) in
        let betaDecayFeeNegVal := extract_value (betaDecayFeeNeg) in
        let netVolume := net_volume (reactions) (lastTimestamp) in
        let totalBaseCoins := 
            get_basecoins (stableCoinState.(reactorState)) in
        (betaDecayFeePosVal) +
        ((betaDecayFeeNegVal) * 
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
        let stableCoins := 
            (baseCoins * (1 - fusion_ratio (state)) * (1 - extract_value (fissionFee))) / (reservecoin_price (state)) in
        let reserveCoins :=
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
            (newReactorState) (stableCoinState.(exchangeRate)).

    Definition fusion_output 
        (stableCoins : StableCoins) 
        (reserveCoins : ReserveCoins) 
        (state : StableCoinState) : R :=

        let baseCoinsFromStableCoins := 
            (stableCoins) * (stablecoin_price (state)) in
        let baseCoinsFromReserveCoins := 
            (reserveCoins) * (reservecoin_price (state)) in
        let baseCoinsReturned := 
            (1 - extract_value (fusionFee)) * (baseCoinsFromReserveCoins + baseCoinsFromStableCoins) in
        baseCoinsReturned.
    

    Definition fusion_reaction
        (stableCoinState : StableCoinState) 
        (stableCoins : StableCoins)
        (reserveCoins : ReserveCoins) : StableCoinState :=
        let baseCoins := fusion_output 
                        (stableCoins) (reserveCoins) (stableCoinState) in
        let oldReactorState := stableCoinState.(reactorState) in
        let newReactorState := Build_ReactorState 
                                (get_basecoins (oldReactorState) - baseCoins)
                                (get_stablecoins (oldReactorState) - stableCoins)
                                (get_reservecoins (oldReactorState) - reserveCoins) 
                                in
        Build_StableCoinState 
            (newReactorState) (stableCoinState.(exchangeRate)).
    
    
    Definition beta_decay_pos_output 
        (reserveCoins : ReserveCoins) 
        (beta_decay_pos_fee : R) 
        (state : StableCoinState) : R :=

        (reserveCoins * (1 - beta_decay_pos_fee) * (reservecoin_price (state))) / stablecoin_price (state).
    
    Definition beta_decay_pos_reaction
        (stableCoinState : StableCoinState) 
        (beta_decay_pos_fee : R)
        (protonsInput : ReserveCoins) : StableCoinState :=
        let neutrons := beta_decay_pos_output
                        (protonsInput) (beta_decay_pos_fee) (stableCoinState) in
        let oldReactorState := stableCoinState.(reactorState) in
        let newReactorState := Build_ReactorState 
                                (get_basecoins (oldReactorState))
                                (get_stablecoins (oldReactorState) + neutrons)
                                (get_reservecoins (oldReactorState) - protonsInput) 
                                in
        Build_StableCoinState 
            (newReactorState) (stableCoinState.(exchangeRate)).

    Definition beta_decay_neg_output 
        (stableCoins : StableCoins) 
        (beta_decay_neg_fee : R) 
        (state : StableCoinState) : R :=

        (stableCoins * (1 - beta_decay_neg_fee) * (stablecoin_price (state))) / reservecoin_price (state).
        
    
    Definition beta_decay_neg_reaction
        (stableCoinState : StableCoinState) 
        (beta_decay_neg_fee : R)
        (neutronsInput : StableCoins) : StableCoinState :=
        let protons := beta_decay_neg_output
                        (neutronsInput) (beta_decay_neg_fee) (stableCoinState) in
        let oldReactorState := stableCoinState.(reactorState) in
        let newReactorState := Build_ReactorState 
                                (get_basecoins (oldReactorState))
                                (get_stablecoins (oldReactorState) - neutronsInput)
                                (get_reservecoins (oldReactorState) + protons) 
                                in
        Build_StableCoinState 
            (newReactorState) (stableCoinState.(exchangeRate)).
    
    (*
     * Theorem related functions
     *)
    
    Definition stablecoins_from_m_basecoins
        (state_0 : State)
        (timestamp : nat)
        (state_1 : State)
        (basecoins : R) 
        (fracProtonsDecay : R) : R :=
    let (stablecoins, reservecoins) := fission_output (basecoins) (state_0.(stableCoinState)) in
    let betaDecayFeePos := beta_decay_pos_fee (state_1.(reactions)) (state_1.(stableCoinState)) (timestamp) in
    let stablecoinsFromDecay := beta_decay_pos_output (reservecoins * fracProtonsDecay) (betaDecayFeePos) (state_1.(stableCoinState)) in
    stablecoins + stablecoinsFromDecay.
    
    (*
     * This functions gives us the number of base coins we have to use for 
     * fission in order to get N stablecoins.
     * state_0: stablecoin state before fission
     * timestamp: time when the beta decay + is initiated
     * state_1: stablecoin state before beta decay +
     * fracProtonsDecay: fraction of reserve coins from fission that are 
     *                   converted to stablecoins
     *)

    Definition base_coins_for_n_stable_coins
        (state_0 : State)
        (timestamp : nat)
        (state_1 : State)
        (stablecoinsRequired : R) 
        (fracProtonsDecay : R) : R :=
        let rInit := reservecoin_price (state_0.(stableCoinState)) in
        let rNew := reservecoin_price (state_1.(stableCoinState)) in
        let sInit := stablecoin_price (state_0.(stableCoinState)) in
        let sNew := stablecoin_price (state_1.(stableCoinState)) in
        let fInit := fusion_ratio (state_0.(stableCoinState)) in
        let betaPlusInit := beta_decay_pos_fee (state_1.(reactions)) (state_1.(stableCoinState)) (timestamp) in
        let fissionFeeVal := extract_value (fissionFee) in
        (rInit * sNew * sInit * stablecoinsRequired) / 
        ((fInit * (1 - fissionFeeVal) * rInit * sNew) + 
        ((1 - fInit) * fracProtonsDecay * (1 - fissionFeeVal) * (1 - betaPlusInit) * rNew * sInit)).

    (*
     * This function returns the effective fee in terms of base coins for the
     * action of selling/buying a stablecoin
     *)
    Definition get_effective_fee
        (timestamp : nat)
        (state_0 : State) 
        (state_1 : State)
        (action : Action) : R :=
        match action with
        | SellStableCoin => 0
        | BuyStableCoin =>
            let baseCoinsForOneStableCoin := base_coins_for_n_stable_coins (state_0) (timestamp) (state_1) (1) (1) in
            let stableCoinPriceBeforeFission := stablecoin_price (state_0.(stableCoinState)) in
            (baseCoinsForOneStableCoin / stableCoinPriceBeforeFission) - 1
        end.
    
    (*
     * This function returns the price of buying/selling a stablecoin in terms
     * of base coins
     *)
    Definition get_primary_market_offer
        (timestamp : nat)
        (state_0 : State) 
        (state_1 : State) 
        (action : Action) : R :=
        match action with
        | BuyStableCoin => 
            base_coins_for_n_stable_coins (state_0) (timestamp) (state_1) (1) (1)
        | SellStableCoin =>  
            (1 + get_effective_fee 
                (timestamp) (state_0) (state_1) (action)) *
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
            | (s_1, t_1, r_1) :: reactions'' =>
                match r_1 with
                | Fission (nuclei) _ _ => 
                    (s_2 = fission_reaction (s_1) (nuclei)) /\ 
                    states_follow (reactions')
                | Fusion (neutrons) (protons) _ =>
                    (s_2 = fusion_reaction (s_1) (neutrons) (protons)) /\ 
                    states_follow (reactions')
                | BetaDecayPos (protons) _ =>
                    let beta_decay_pos_fee_val := 
                    beta_decay_pos_fee (reactions'') (s_1) (t_1) in
                    (s_2 = beta_decay_pos_reaction (s_1) (beta_decay_pos_fee_val) (protons)) /\
                    states_follow (reactions')
                | BetaDecayNeg (neutrons) _ =>
                    let beta_decay_neg_fee_val := 
                    beta_decay_neg_fee (reactions'') (s_1) (t_1) in
                    (s_2 = beta_decay_neg_reaction (s_1) (beta_decay_neg_fee_val) (neutrons)) /\
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
            | (s, t, r) :: reactions' =>
                match r with
                | Fission (nuclei) _ _ => 
                    currStableCoinState = fission_reaction (s) (nuclei)
                | Fusion (neutrons) (protons) _ => 
                    currStableCoinState = 
                    fusion_reaction (s) (neutrons) (protons)
                | BetaDecayPos (protons) _ =>
                    let beta_decay_pos_fee_val := 
                    beta_decay_pos_fee (reactions') (s) (t) in
                    currStableCoinState = 
                    beta_decay_pos_reaction 
                    (s) (beta_decay_pos_fee_val) (protons)
                | BetaDecayNeg (neutrons) _ =>
                    let beta_decay_neg_fee_val := 
                    beta_decay_neg_fee (reactions') (s) (t) in
                    currStableCoinState = 
                    beta_decay_neg_reaction 
                    (s) (beta_decay_neg_fee_val) (neutrons)
                end
            end.


    (* (s1, t1, r1) , (s2, t2, r2)
    
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

End Functions. 












