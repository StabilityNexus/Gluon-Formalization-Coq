(*
 * Importing the Libraries
 *)
From StableCoinFormalization Require Export Datatypes.
From StableCoinFormalization Require Export HelperFunctions.

Module Functions.
    Import Datatypes.
    Import HelperFunctions.

    (*
     * Defining Parameters
     *)
    
    Parameter qStar : QStar.
    Parameter fissionFee : FissionFee.
    Parameter fusionFee : FusionFee.
    Parameter betaDecayFeePos : BetaDecayFeePos.
    Parameter betaDecayFeeNeg : BetaDecayFeeNeg.
    Parameter timePeriod : TimePeriod.

    Axiom betaDecayFee_assumption :
        let betaDecayFeePosVal := extract_value (betaDecayFeePos) in
        let betaDecayFeeNegVal := extract_value (betaDecayFeeNeg) in
        (ltb 0 (betaDecayFeePosVal + betaDecayFeeNegVal) = true) /\ 
        (leb (betaDecayFeePosVal + betaDecayFeeNegVal) 1 = true).
    
    (*
     * Defining Functions
     *)

    Definition target_price (state : StableCoinState) : float :=
        extract_value (state.(exchangeRate)).

    Definition fusion_ratio (state : StableCoinState) : float :=
        let qStarVal := extract_value (qStar) in
        let nucleiVal := extract_value (state.(reactorState).(nuclei)) in
        let neutronsVal := extract_value (state.(reactorState).(neutrons)) in
        let exchangeRateVal := extract_value (state.(exchangeRate)) in
        if eqb (nucleiVal) (0)
        then
            qStarVal
        else 
            float_min 
            (qStarVal)
            (div (mul (neutronsVal) (exchangeRateVal)) (qStarVal)).
    
    Definition neutron_price (state : StableCoinState) : float :=
        let fusionRatio := fusion_ratio (state) in
        let baseCoinsVal := extract_value (state.(reactorState).(nuclei)) in
        let stableCoinsVal := extract_value (state.(reactorState).(neutrons)) in
        div (mul (fusionRatio) (baseCoinsVal)) (baseCoinsVal).

    Definition proton_price (state : StableCoinState) : float :=
        let fusionRatio := fusion_ratio (state) in
        let baseCoinsVal := extract_value (state.(reactorState).(nuclei)) in
        let reserveCoinsVal := extract_value (state.(reactorState).(protons)) in
        div (mul (sub (1) (fusionRatio)) (baseCoinsVal)) (reserveCoinsVal).
    
    Definition liabilities (state : StableCoinState) : float :=
        let fusionRatio := fusion_ratio (state) in
        let baseCoinsVal := extract_value (state.(reactorState).(nuclei)) in
        mul (fusionRatio) (baseCoinsVal).
    
    Definition reserve_ratio (state : StableCoinState) : float :=
        let fusionRatio := fusion_ratio (state) in
        div (1) (fusionRatio).
    
    Definition equity (state : StableCoinState) : float :=
        let fusionRatio := fusion_ratio (state) in
        let baseCoinsVal := extract_value (state.(reactorState).(nuclei)) in
        mul (sub (1) (fusionRatio)) (baseCoinsVal).
    
    (*
     * The reaction stored at the head of the trace has timestamp equal to the 
     * length of the trace. The reaction stored at the very end has timestamp 1.
     * elemsToSkip will equal 0 if lastTimestamp > totalLength.
     * firstn elemsToSelect slice will return the whole slice if elemsToSelect > length (slice)
     *)
    Definition reactions_slice (state : State) (lastTimestamp : nat) : Trace :=
        let totalReactions := state.(reactions) in
        let totalLength := length totalReactions in
        let elemsToSkip := totalLength - lastTimestamp in
        let elemsToSelect := timePeriod + 1 in
        let slice := skipn elemsToSkip totalReactions in
        firstn elemsToSelect slice.

    Definition beta_pos_reactions (state : State) (lastTimestamp : nat) : Trace :=
        let slice := reactions_slice (state) (lastTimestamp) in
        filter (fun x => match x with
                        | (_, BetaDecayPos _ _) => true
                        | _ => false
                        end) slice.
    
    Definition beta_neg_reactions (state : State) (lastTimestamp : nat) : Trace :=
        let slice := reactions_slice (state) (lastTimestamp) in
        filter (fun x => match x with
                        | (_, BetaDecayNeg _ _) => true
                        | _ => false
                        end) slice.
    
    Definition volume_beta_pos_reactions (state : State) (lastTimestamp : nat) : float :=
        let betaPosReactions := beta_pos_reactions (state) (lastTimestamp) in
        fold_right (fun x acc => match x with
                                | (stableCoinState, BetaDecayPos protons _) => add (acc) (mul (extract_value (protons)) (proton_price (stableCoinState)))
                                | _ => acc
                                end) zero betaPosReactions.

    Definition volume_beta_neg_reactions (state : State) (lastTimestamp : nat) : float :=
        let betaNegReactions := beta_neg_reactions (state) (lastTimestamp) in
        fold_right (fun x acc => match x with
                                | (stableCoinState, BetaDecayNeg neutrons _) => add (acc) (mul (extract_value (neutrons)) (neutron_price (stableCoinState)))
                                | _ => acc
                                end) zero betaNegReactions.
                                
    Definition net_volume (state : State) (lastTimestamp : nat) : float :=
        let betaPosVolume := volume_beta_pos_reactions (state) (lastTimestamp) in
        let betaNegVolume := volume_beta_neg_reactions (state) (lastTimestamp) in
        sub betaPosVolume betaNegVolume.
    
    Definition beta_decay_pos_fee (state : State) (lastTimestamp : nat) : float :=
        let betaDecayFeePosVal := extract_value (betaDecayFeePos) in
        let betaDecayFeeNegVal := extract_value (betaDecayFeeNeg) in
        let netVolume := net_volume (state) (lastTimestamp) in
        let totalBaseCoins := extract_value (state.(stableCoinState).(reactorState).(nuclei)) in
        add (betaDecayFeePosVal) (mul (betaDecayFeeNegVal) (div (float_max (netVolume) (zero)) (totalBaseCoins))).
    
    Definition beta_decay_neg_fee (state : State) (lastTimestamp : nat) : float :=
        let betaDecayFeePosVal := extract_value (betaDecayFeePos) in
        let betaDecayFeeNegVal := extract_value (betaDecayFeeNeg) in
        let netVolume := net_volume (state) (lastTimestamp) in
        let totalBaseCoins := extract_value (state.(stableCoinState).(reactorState).(nuclei)) in
        add (betaDecayFeePosVal) (mul (betaDecayFeeNegVal) (div (float_max (mul (netVolume) (-1)) (zero)) (totalBaseCoins))).
    
    Definition fission_output (baseCoins : BaseCoins) (state : StableCoinState) : (float * float) :=
        let stableCoinsCirculation := extract_value (state.(reactorState).(neutrons)) in
        let reserveCoinsCirculation := extract_value (state.(reactorState).(protons)) in
        let baseCoinsContract := extract_value (state.(reactorState).(nuclei)) in
        let fissionFeeVal := extract_value (fissionFee) in
        let baseCoinsVal := extract_value (baseCoins) in
        let stableCoins := mul (mul (baseCoinsVal) (sub (1) (fissionFeeVal))) (div (stableCoinsCirculation) (baseCoinsContract)) in
        let reserveCoins := mul (mul (baseCoinsVal) (sub (1) (fissionFeeVal))) (div (reserveCoinsCirculation) (baseCoinsContract)) in
        (stableCoins, reserveCoins).

    Definition fusion_output (stableCoins : StableCoins) 
                            (reserveCoins : ReserveCoins) 
                            (state : StableCoinState) : float :=
        let fusionFeeVal := extract_value (fusionFee) in
        let stableCoinsVal := extract_value (stableCoins) in
        let reserveCoinsVal := extract_value (reserveCoins) in
        let baseCoinsFromStableCoins := mul (stableCoinsVal) (neutron_price (state)) in
        let baseCoinsFromReserveCoins := mul (reserveCoinsVal) (proton_price (state)) in
        let baseCoinsReturned := mul (sub (1) (fusionFeeVal)) (add (baseCoinsFromReserveCoins) (baseCoinsFromStableCoins)) in
        baseCoinsReturned.
    
    
    Definition beta_decay_pos_output (protonsInput : ReserveCoins) (beta_decay_pos_fee : float) (state : StableCoinState) : float :=
        let protonsVal := extract_value (protonsInput) in
        let fusionRatio := fusion_ratio (state) in
        let neutronsCirculation := extract_value (state.(reactorState).(neutrons)) in
        let protonsCirculation := extract_value (state.(reactorState).(protons)) in
        mul (mul (mul (protonsVal) (sub (1) (beta_decay_pos_fee))) (div (sub (1) (fusionRatio)) (fusionRatio))) (div (neutronsCirculation) (protonsCirculation)).

    Definition beta_decay_neg_output (neutronsInput : StableCoins) (beta_decay_neg_fee : float) (state : StableCoinState) : float :=
        let neutronsVal := extract_value (neutronsInput) in
        let fusionRatio := fusion_ratio (state) in
        let neutronsCirculation := extract_value (state.(reactorState).(neutrons)) in
        let protonsCirculation := extract_value (state.(reactorState).(protons)) in
        mul (mul (mul (neutronsVal) (sub (1) (beta_decay_neg_fee))) (div (fusionRatio) (sub (1) (fusionRatio)))) (div (protonsCirculation) (neutronsCirculation)).
    


    (*
     * Theorem related functions
     *)
    Definition primary_market_stable_coin_price (stableCoinState : StableCoinState) : float :=
        zero.
        
    Definition is_rational_choice (secondaryMarketAction : SecondaryMarketAction) (stableCoinState : StableCoinState) : bool :=
        let (SellStableCoin, baseCoins) := secondaryMarketAction in
        let primaryMarketStableCoinPrice := primary_market_stable_coin_price (stableCoinState) in
        let baseCoinsVal := extract_value (baseCoins) in
        if ltb (baseCoinsVal) (primaryMarketStableCoinPrice)
        then true
        else false. 

End Functions.












