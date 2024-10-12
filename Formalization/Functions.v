(*
 * Importing the Libraries
 *)
From StableCoinFormalization Require Export Datatypes.
From StableCoinFormalization Require Export HelperFunctions.

Module Functions.
    Import Qminmax.
    Import Datatypes.
    Import HelperFunctions.

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
    
    (*
     * Defining Functions
     *)

    Definition target_price 
        (state : StableCoinState) : BaseCoins :=

        state.(exchangeRate).

    Definition fusion_ratio 
        (state : StableCoinState) : QStar :=

        let upper_bound_proof := qstar_to_posq_lt_1 (qStar) in
        let nucleiVal := get_nuclei (state.(reactorState)) in
        let neutronsVal := get_neutrons (state.(reactorState)) in
        let exchangeRateVal := get_exchange_rate (state) in
        let qStarPosQ := qstar_to_posq (qStar) in
        let otherValue := (neutronsVal *p exchangeRateVal) //p nucleiVal in
        let proof := 
            a_lt_impl_a_lt_or_b_lt 
            (qStarPosQ) (otherValue) (1) (upper_bound_proof) in  
        min_posq (qStarPosQ) (otherValue) (1) (proof).
    
    Definition neutron_price 
        (state : StableCoinState) : PosQ :=

        let fusionRatio := qstar_to_posq (fusion_ratio (state)) in
        let baseCoinsVal := get_nuclei (state.(reactorState)) in
        let stableCoinsVal := get_neutrons (state.(reactorState)) in
        (fusionRatio *p baseCoinsVal) //p stableCoinsVal.

    Definition proton_price 
        (state : StableCoinState) : PosQ :=

        let fusionRatio := qstar_to_posq (fusion_ratio (state)) in
        let proof := qstar_lt_1 (fusion_ratio (state)) in
        let baseCoinsVal := get_nuclei (state.(reactorState)) in
        let reserveCoinsVal := get_protons (state.(reactorState)) in
        ((sub_posq (one_posq) (fusionRatio) (proof)) *p baseCoinsVal) //p reserveCoinsVal.
    
    Definition liabilities 
        (state : StableCoinState) : Q :=

        let fusionRatio := extract_value (fusion_ratio (state)) in
        let baseCoinsVal := extract_value (get_nuclei (state.(reactorState))) in
        fusionRatio * baseCoinsVal.
    
    Definition reserve_ratio 
        (state : StableCoinState) : Q :=

        let fusionRatio := extract_value (fusion_ratio (state)) in
        1 / fusionRatio.
    
    Definition equity 
        (state : StableCoinState) : Q :=

        let fusionRatio := extract_value (fusion_ratio (state)) in
        let baseCoinsVal := extract_value (get_nuclei (state.(reactorState))) in
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
                | (_, t, _) => ((lastTimestamp - timePeriod) <=? t) && 
                            (t <=? lastTimestamp)
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
        (lastTimestamp : nat) : Q :=

        let betaPosReactions := beta_pos_reactions (reactions) (lastTimestamp) in
        fold_right (fun x acc => match x with
                                | (stableCoinState, _, BetaDecayPos protons _) =>  
                                    (acc) + 
                                    (extract_value (protons) * 
                                    (extract_value (proton_price (stableCoinState))))
                                | _ => acc
                                end) 0 betaPosReactions.

    Definition volume_beta_neg_reactions 
        (reactions : Trace) 
        (lastTimestamp : nat) : Q :=

        let betaNegReactions := beta_neg_reactions (reactions) (lastTimestamp) in
        fold_right (fun x acc => match x with
                                | (stableCoinState, _, BetaDecayNeg neutrons _) => 
                                    (acc) + 
                                    (extract_value (neutrons) * 
                                     extract_value (neutron_price (stableCoinState)))
                                | _ => acc
                                end) 0 betaNegReactions.
                                
    Definition net_volume 
        (reactions : Trace) 
        (lastTimestamp : nat) : Q :=

        let betaPosVolume := 
            volume_beta_pos_reactions (reactions) (lastTimestamp) in
        let betaNegVolume := 
            volume_beta_neg_reactions (reactions) (lastTimestamp) in
        betaPosVolume - betaNegVolume.
    
    Definition beta_decay_pos_fee  
        (reactions : Trace)
        (stableCoinState : StableCoinState) 
        (lastTimestamp : nat) : Q :=

        let betaDecayFeePosVal := extract_value (betaDecayFeePos) in
        let betaDecayFeeNegVal := extract_value (betaDecayFeeNeg) in
        let netVolume := net_volume (reactions) (lastTimestamp) in
        let totalBaseCoins := 
            extract_value (get_nuclei (stableCoinState.(reactorState))) in
        (betaDecayFeePosVal) +  
        ((betaDecayFeeNegVal) *  
         ((Qmax (netVolume) (0)) / totalBaseCoins)).
    
    Definition beta_decay_neg_fee 
        (reactions : Trace)
        (stableCoinState : StableCoinState) 
        (lastTimestamp : nat) : Q :=

        let betaDecayFeePosVal := extract_value (betaDecayFeePos) in
        let betaDecayFeeNegVal := extract_value (betaDecayFeeNeg) in
        let netVolume := net_volume (reactions) (lastTimestamp) in
        let totalBaseCoins := 
            extract_value (get_nuclei (stableCoinState.(reactorState))) in
        (betaDecayFeePosVal) +
        ((betaDecayFeeNegVal) * 
         ((Qmax (netVolume * -1) (0)) / (totalBaseCoins))).
    
    Definition fission_output 
        (baseCoins : BaseCoins) 
        (state : StableCoinState) : (StableCoins * ReserveCoins) :=
        let stableCoinsCirculation := 
            get_neutrons (state.(reactorState)) in
        let reserveCoinsCirculation := 
            get_protons (state.(reactorState)) in
        let baseCoinsContract := 
            get_nuclei (state.(reactorState)) in
        let stableCoins := 
            (baseCoins *p (sub_posq (one_posq) (qstar_to_posq (fissionFee)) (qstar_lt_1 (fissionFee)))) *p
            (stableCoinsCirculation //p baseCoinsContract) in
        let reserveCoins := 
            (baseCoins *p (sub_posq (one_posq) (qstar_to_posq (fissionFee)) (qstar_lt_1 (fissionFee)))) *p 
            (reserveCoinsCirculation //p baseCoinsContract) in
        (stableCoins, reserveCoins).

    Definition fission_reaction
        (stableCoinState : StableCoinState) 
        (baseCoins : BaseCoins) : StableCoinState :=
        let (stableCoins, reserveCoins) := fission_output (baseCoins) 
                                            (stableCoinState) in
        let oldReactorState := stableCoinState.(reactorState) in
        let newReactorState := Build_ReactorState 
                                (get_nuclei (oldReactorState) +p baseCoins)
                                (get_neutrons (oldReactorState) +p stableCoins)
                                (get_protons (oldReactorState) +p reserveCoins) 
                                in
        Build_StableCoinState 
            (newReactorState) (stableCoinState.(exchangeRate)).

    Definition fusion_output 
        (stableCoins : Fraction) 
        (reserveCoins : Fraction) 
        (state : StableCoinState) : BaseCoins :=

        let baseCoinsFromStableCoins := 
            (fraction_to_posq (stableCoins) *p get_neutrons (state.(reactorState))) *p 
            (neutron_price (state)) in
        let baseCoinsFromReserveCoins := 
            (fraction_to_posq (reserveCoins) *p get_protons (state.(reactorState))) *p 
            (proton_price (state)) in
        let baseCoinsReturned := 
            (sub_posq (one_posq) (qstar_to_posq (fusionFee)) (qstar_lt_1 (fusionFee))) *p 
            (baseCoinsFromReserveCoins +p baseCoinsFromStableCoins) in
        baseCoinsReturned.
    
    Theorem fusion_returns_portion_of_current_basecoins :
        forall 
        (stableCoins : Fraction) 
        (reserveCoins : Fraction)
        (state : StableCoinState),
            extract_value (fusion_output (stableCoins) (reserveCoins) (state)) < extract_value (get_nuclei (state.(reactorState))).
    Proof.
        intros.
        assert (fusion_output (stableCoins) (reserveCoins) (state) < get_nuclei (reactorState (state))) as H.
    
    Definition fusion_reaction
        (stableCoinState : StableCoinState) 
        (stableCoins : StableCoins)
        (reserveCoins : ReserveCoins) : StableCoinState :=
        let baseCoins := fusion_output 
                        (stableCoins) (reserveCoins) (stableCoinState) in
        let oldReactorState := stableCoinState.(reactorState) in
        let newReactorState := Build_ReactorState 
                                (get_nuclei (oldReactorState) - baseCoins)
                                (get_neutrons (oldReactorState) - stableCoins)
                                (get_protons (oldReactorState) - reserveCoins) 
                                in
        Build_StableCoinState 
            (newReactorState) (stableCoinState.(exchangeRate)).
    
    
    Definition beta_decay_pos_output 
        (protonsInput : ReserveCoins) 
        (beta_decay_pos_fee : Q) 
        (state : StableCoinState) : Q :=

        let protonsVal := protonsInput in
        let fusionRatio := fusion_ratio (state) in
        let neutronsCirculation := 
            get_neutrons (state.(reactorState)) in
        let protonsCirculation := 
            get_protons (state.(reactorState)) in
        ((protonsVal * (1 - beta_decay_pos_fee)) *
        ((1 - fusionRatio) / fusionRatio)) * 
        (neutronsCirculation / protonsCirculation).
    
    Definition beta_decay_pos_reaction
        (stableCoinState : StableCoinState) 
        (beta_decay_pos_fee : Q)
        (protonsInput : ReserveCoins) : StableCoinState :=
        let neutrons := beta_decay_pos_output
                        (protonsInput) (beta_decay_pos_fee) (stableCoinState) in
        let oldReactorState := stableCoinState.(reactorState) in
        let newReactorState := Build_ReactorState 
                                (get_nuclei (oldReactorState))
                                (get_neutrons (oldReactorState) + neutrons)
                                (get_protons (oldReactorState) - protonsInput) 
                                in
        Build_StableCoinState 
            (newReactorState) (stableCoinState.(exchangeRate)).

    Definition beta_decay_neg_output 
        (neutronsInput : StableCoins) 
        (beta_decay_neg_fee : Q) 
        (state : StableCoinState) : Q :=

        let neutronsVal := neutronsInput in
        let fusionRatio := fusion_ratio (state) in
        let neutronsCirculation := 
            get_neutrons (state.(reactorState)) in
        let protonsCirculation := 
            get_protons (state.(reactorState)) in 
        ((neutronsVal * (1 - beta_decay_neg_fee))) * 
        (fusionRatio / (1 - fusionRatio)) * 
        (protonsCirculation / neutronsCirculation).
    
    Definition beta_decay_neg_reaction
        (stableCoinState : StableCoinState) 
        (beta_decay_neg_fee : Q)
        (neutronsInput : StableCoins) : StableCoinState :=
        let protons := beta_decay_neg_output
                        (neutronsInput) (beta_decay_neg_fee) (stableCoinState) in
        let oldReactorState := stableCoinState.(reactorState) in
        let newReactorState := Build_ReactorState 
                                (get_nuclei (oldReactorState))
                                (get_neutrons (oldReactorState) - neutronsInput)
                                (get_protons (oldReactorState) + protons) 
                                in
        Build_StableCoinState 
            (newReactorState) (stableCoinState.(exchangeRate)).
    
    (*
     * Theorem related functions
     *)

    (*
     * This function returns the effective fee in terms of base coins for the
     * action of selling/buying a stablecoin
     *)
    Definition get_effective_fee
        (timestamp : nat)
        (state_0 : State) 
        (state_1 : State)
        (action : Action) : Q :=
        match action with
        | SellStableCoin => 0
        | BuyStableCoin =>
            let proton_price_0 := proton_price (state_0.(stableCoinState)) in
            let neutron_price_0 := neutron_price (state_0.(stableCoinState)) in
            let proton_price_1 := proton_price (state_1.(stableCoinState)) in
            let neutron_price_1 := neutron_price (state_1.(stableCoinState)) in
            let fusion_ratio_0 := fusion_ratio (state_0.(stableCoinState)) in
            let fission_fee_val := extract_value (fissionFee) in
            let beta_decay_pos_fee_val := 
                beta_decay_pos_fee (state_1.(reactions)) 
                (state_1.(stableCoinState)) (timestamp) in
            ((proton_price_0 * neutron_price_1) / 
            ((fusion_ratio_0 * (1 - fission_fee_val) * 
                proton_price_0 * neutron_price_1) + 
            ((1 - fusion_ratio_0) * (1 - fission_fee_val) * 
            (1 - beta_decay_pos_fee_val) * proton_price_1 * neutron_price_0))) 
            - 1
        end.
    
    (*
     * This function returns the price of buying/selling a stablecoin in terms
     * of base coins
     *)
    Definition get_primary_market_offer
        (timestamp : nat)
        (state_0 : State) 
        (state_1 : State) 
        (action : Action) : Q :=
        match action with
        | BuyStableCoin => 
            (1 + get_effective_fee 
                (timestamp) (state_0) (state_1) (action)) *
            (neutron_price (state_0.(stableCoinState)))
        | SellStableCoin =>  
            (1 + get_effective_fee 
                (timestamp) (state_0) (state_1) (action)) *
            (neutron_price (state_0.(stableCoinState)))
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
        (primaryMarketOffer : Q) 
        (secondaryMarketOffer : Q) : Choice :=
        match action with
        | BuyStableCoin =>
            match secondaryMarketOffer ?= primaryMarketOffer with
            | Lt => Secondary
            | _ => Primary
            end
        | SellStableCoin =>
            match secondaryMarketOffer ?= primaryMarketOffer with
            | Gt => Secondary
            | _ => Primary
            end
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












