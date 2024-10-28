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
    
    Axiom exchangerate_assumption :
        forall (e : ExchangeRate),
            e > 0.

    
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
    
    Lemma add_frac_real :
        forall a b c d : R, b <> 0 -> d <> 0 ->
            (a / b) + (c / d) = ((a * d) + (c * b)) / (b * d).
    Proof.
        intros a b c d Hb_nonzero Hd_nonzero. unfold Rdiv.
        rewrite Rmult_comm with (r1 := (a * d + c * b)).
        rewrite Rmult_plus_distr_l with (r1 := / (b * d)).
        rewrite Rmult_comm with (r1 := / (b * d)).
        rewrite Rmult_comm with (r1 := / (b * d)).
        assert (forall a b : R, a * /b = a / b) as H.
        { intros. unfold Rdiv. reflexivity. }
        rewrite H with (a := (a * d)) (b := (b * d)).
        rewrite H with (a := (c * b)) (b := (b * d)).
        rewrite Rdiv_mult_r_r with (r := d).
        rewrite Rmult_comm with (r1 := b).
        rewrite Rdiv_mult_r_r with (r := b).
        - rewrite H. rewrite H. reflexivity.
        - apply Hb_nonzero.
        - apply Hd_nonzero.
    Qed.

    Lemma fusion_ratio_gt_0 :
        forall stableCoinState : StableCoinState,
            fusion_ratio (stableCoinState) > 0.
    Proof.
        intros. unfold fusion_ratio. unfold Rmin.
        destruct (Rle_dec (extract_value qStar)
        (get_stablecoins (reactorState stableCoinState0) *
         get_exchange_rate stableCoinState0 /
         get_basecoins (reactorState stableCoinState0))).
        - destruct qStar. simpl. destruct a. apply r0.
        - destruct stableCoinState0. destruct reactorState.
        simpl. 
        destruct reactorstate_assumption with 
        (b := baseCoins0) (r := reserveCoins0) (s := stableCoins0) 
        as [H1 [H2 H3]].
        assert (exchangeRate0 > 0) as H4. { apply exchangerate_assumption. }
        apply Rdiv_pos_pos.
            * nra.
            * nra.
    Qed.

    Lemma fusion_ratio_lt_1 :
        forall stableCoinState : StableCoinState,
            fusion_ratio (stableCoinState) < 1.
    Proof.
        intros. unfold fusion_ratio. destruct qStar. simpl.
        apply Rle_lt_trans with (r2 := x).
        - apply Rmin_l.
        - destruct a. apply H0.
    Qed.


    Lemma stablecoin_price_gt_0 :
        forall state : State,
            stablecoin_price (stableCoinState state) > 0.
    Proof.
        intros. destruct state. unfold stablecoin_price. simpl.
        apply Rdiv_pos_pos.
        - apply Rmult_pos_pos.
            * apply fusion_ratio_gt_0.
            * destruct stableCoinState0. destruct reactorState0. simpl.
            destruct reactorstate_assumption with 
            (b := baseCoins0) (r := reserveCoins0) (s := stableCoins0) 
            as [H1 [H2 H3]]. nra.
        - destruct stableCoinState0. destruct reactorState0. simpl.
        destruct reactorstate_assumption with 
        (b := baseCoins0) (r := reserveCoins0) (s := stableCoins0) 
        as [H1 [H2 H3]]. nra.
    Qed.
        
    Lemma reservecoin_price_gt_0 :
        forall state : State,
            reservecoin_price (stableCoinState state) > 0.
    Proof.
        intros. destruct state. destruct stableCoinState. 
        destruct reactorState0. unfold reservecoin_price. unfold fusion_ratio.
        destruct reactorstate_assumption with 
        (b := baseCoins0) (r := reserveCoins0) (s := stableCoins0) 
        as [H1 [H2 H3]].
        simpl. apply Rdiv_pos_pos.
        - apply Rmult_pos_pos.
            * apply Rgt_minus. apply Rgt_ge_trans with (r2 := extract_value qStar).
            destruct qStar. simpl. destruct a. apply H0.
            apply Rle_ge. apply Rmin_l.
            * nra.
        - nra.
    Qed. 

    Lemma a_lt_c_strict : 
        forall a b c : R, 0 < a -> 0 < b -> a + b <= c -> a < c.
    Proof.
        intros a b c Ha Hb Hsum.
        (* We know a + b <= c and 0 < b, so a must be strictly less than c *)
        apply Rlt_le_trans with (r2 := a + b).
        - nra.
        - apply Hsum. 
    Qed.

    Lemma net_volume_lt_basecoins :
        forall (state : State) (timestamp : nat),
            net_volume (state.(reactions)) (timestamp) < ((state.(stableCoinState)).(reactorState)).(baseCoins).
    Proof.
    Admitted.


    Lemma beta_decay_pos_fee_lt_1 :
        forall (state : State) (timestamp : nat),
            beta_decay_pos_fee (reactions (state)) (stableCoinState (state)) (timestamp) < 1.
    Proof.
        intros. assert (net_volume (state.(reactions)) (timestamp) < ((state.(stableCoinState)).(reactorState)).(baseCoins)) as H.
        { apply net_volume_lt_basecoins. }
        destruct state. destruct stableCoinState0. destruct reactorState0.
        unfold beta_decay_pos_fee. simpl. simpl in H. unfold Rmax. destruct (Rle_dec (net_volume reactions0 timestamp) 0).
        - unfold Rdiv. rewrite Rmult_0_l. rewrite Rmult_0_r. rewrite Rplus_0_r.
        destruct betaDecayFee_assumption as [H1 H2].
        apply a_lt_c_strict with (b := extract_value betaDecayFeeNeg).
            * destruct betaDecayFeePos. simpl. nra.
            * destruct betaDecayFeeNeg. simpl. nra.
            * apply H2.
        - apply Rlt_le_trans with (r2 := extract_value betaDecayFeePos + extract_value betaDecayFeeNeg).
            * apply Rplus_lt_compat_l with (r := extract_value betaDecayFeePos).
            rewrite <- Rmult_1_r. apply Rmult_lt_compat_l with (r := extract_value betaDecayFeeNeg).
            destruct betaDecayFeeNeg. simpl. apply r. unfold Rdiv.
            apply Rmult_lt_reg_r with (r := baseCoins0).
                + destruct reactorstate_assumption with 
                (b := baseCoins0) (r := reserveCoins0) (s := stableCoins0) 
                as [H1 [H2 H3]]. apply H1.
                + rewrite Rmult_assoc. rewrite Rinv_l. rewrite Rmult_1_r.
                rewrite Rmult_1_l. simpl in H. apply H. 
                destruct reactorstate_assumption with 
                (b := baseCoins0) (r := reserveCoins0) (s := stableCoins0) 
                as [H1 [H2 H3]]. unfold not. intros. nra.
            * destruct betaDecayFee_assumption as [H1 H2]. apply H2.
    Qed.

    Theorem base_coins_for_n_stable_coins_correctness : 
        forall
            (state_0 state_1 : State) 
            (timestamp : nat) 
            (stablecoinsRequired : R)
            (fracProtonsDecay : R)
            (fracPos : 0 < fracProtonsDecay < 1),
        stablecoins_from_m_basecoins (state_0) (timestamp) (state_1) 
        (base_coins_for_n_stable_coins (state_0) (timestamp) 
        (state_1) (stablecoinsRequired) (fracProtonsDecay)) (fracProtonsDecay) = 
        stablecoinsRequired.
    Proof.
        intros. unfold base_coins_for_n_stable_coins.
        unfold stablecoins_from_m_basecoins. unfold beta_decay_pos_output. 
        unfold fission_output.
        set (r := (reservecoin_price (stableCoinState state_0))).
        set (s' := stablecoin_price (stableCoinState state_1)).
        set (s := stablecoin_price (stableCoinState state_0)).
        set (N := stablecoinsRequired).
        set (f := fusion_ratio (stableCoinState state_0)).
        set (fissionFeeVal := extract_value fissionFee).
        set (
                betaPlusInit := 
                beta_decay_pos_fee (reactions state_1) (stableCoinState state_1) 
                timestamp
            ).
        set (r' := reservecoin_price (stableCoinState state_1)).
        set (baseCoins := r * s' * s * N /
        (f * (1 - fissionFeeVal) * r * s' +
         (1 - f) * fracProtonsDecay *
         (1 - fissionFeeVal) * (1 - betaPlusInit) *
         r' * s)).
        rewrite <- Rmult_div_assoc with (r2 := 1 - fissionFeeVal).
        rewrite Rmult_assoc with (r2 := f).
        assert (baseCoins * (1 - f) * (1 - fissionFeeVal) /
        r * fracProtonsDecay * (1 - betaPlusInit) *
        r' / s' = baseCoins * (1 - f) * (1 - fissionFeeVal) /
        r * (fracProtonsDecay * (1 - betaPlusInit) *
        r') / s') as H.
        { lra. } rewrite H. rewrite <- Rmult_div_swap with (r3 := r). simpl.
        rewrite <- Rdiv_mult_distr with (r2 := r).
        assert (baseCoins * (1 - f) * (1 - fissionFeeVal) *
        (fracProtonsDecay * (1 - betaPlusInit) * r') /
        (r * s') = baseCoins * (((1 - f) * (1 - fissionFeeVal) * fracProtonsDecay * (1 - betaPlusInit) * r') / (r * s'))) as H1.
        { nra. } rewrite H1.
        rewrite <- Rmult_plus_distr_l with (r1 := baseCoins).
        assert (f * ((1 - fissionFeeVal) / s) = f * (1 - fissionFeeVal) / s) as H2.
        { nra. } rewrite H2.
        rewrite add_frac_real with (b := s) (d := r * s').
        rewrite Rmult_assoc with (r3 := fracProtonsDecay).
        rewrite Rmult_comm with (r1 := 1 - fissionFeeVal).
        rewrite <- Rmult_assoc with (r3 := 1 - fissionFeeVal).
        rewrite <- Rmult_assoc with (r3 := s').
        unfold baseCoins.
        set (denom := f * (1 - fissionFeeVal) * r * s' +
        (1 - f) * fracProtonsDecay *
        (1 - fissionFeeVal) * (1 - betaPlusInit) *
        r' * s). unfold Rdiv. rewrite <- Rmult_assoc with (r3 := / (s * (r * s'))).
        rewrite Rmult_assoc with (r3 := denom).
        rewrite Rmult_inv_l with (r := denom).
        rewrite Rmult_1_r. rewrite Rmult_comm with (r1 := s).
        assert (forall a b : R, a * /b = a / b) as H3.
        { intros. unfold Rdiv. reflexivity. }
        rewrite H3 with (a := r * s' * s * N).
        rewrite Rmult_div_r. 
        - reflexivity.
        - unfold not. intros. assert (r * s' * s > 0) as H4.
        { 
            unfold r. unfold s'. unfold s. apply Rmult_pos_pos.
            - apply Rmult_pos_pos.
                * apply reservecoin_price_gt_0.
                * apply stablecoin_price_gt_0.
            - apply stablecoin_price_gt_0. 
        } nra. 
        - unfold not. intros.
        assert (denom > 0) as denom_gt_zero.
        {
            unfold denom. apply Rplus_pos_nneg.
            - apply Rmult_pos_pos. apply Rmult_pos_pos. apply Rmult_pos_pos.
                * unfold f. apply fusion_ratio_gt_0.
                * apply Rgt_minus. unfold fissionFeeVal. destruct fissionFee.
                simpl. destruct a. apply r1.
                * unfold r. apply reservecoin_price_gt_0.
                * unfold s'. apply stablecoin_price_gt_0.
            - apply Rle_ge. apply Rmult_le_pos. apply Rmult_le_pos. apply Rmult_le_pos.
            apply Rmult_le_pos. apply Rmult_le_pos.
                * apply Rge_le. apply Rge_minus. apply Rgt_ge. apply Rlt_gt.
                unfold f. apply fusion_ratio_lt_1.
                * apply Rlt_le. destruct fracPos. apply H3.
                * apply Rge_le. apply Rge_minus. apply Rgt_ge. apply Rlt_gt.
                unfold fissionFeeVal. destruct fissionFee. simpl. destruct a. apply r1.
                * apply Rge_le. apply Rge_minus. apply Rgt_ge. apply Rlt_gt.
                unfold betaPlusInit. apply beta_decay_pos_fee_lt_1.
                * apply Rlt_le. unfold r'. apply reservecoin_price_gt_0.
                * apply Rlt_le. unfold s. apply stablecoin_price_gt_0.
        } nra.
        - unfold s. unfold not. intros. assert (stablecoin_price
        (stableCoinState state_0) > 0) as H3.
        { apply stablecoin_price_gt_0. } nra.
        - unfold r. unfold s'. unfold not. intros. assert (reservecoin_price
        (stableCoinState state_0) * stablecoin_price (stableCoinState state_1) > 0).
        { apply Rmult_pos_pos. apply reservecoin_price_gt_0. apply stablecoin_price_gt_0. }
        nra. 
    Qed.  

        
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












