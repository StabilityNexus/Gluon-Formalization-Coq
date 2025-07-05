(*
* Importing the Libraries
*)
From StableCoinFormalization Require Export Datatypes.
From StableCoinFormalization Require Export HelperFunctions.
From StableCoinFormalization Require Export Functions.
From StableCoinFormalization Require Export HelperLemmas.
Require Export Lra.
Local Open Scope R_scope.

Module FunctionProofs.
    Import Datatypes.
    Import Functions.
    Import HelperFunctions.
    Import HelperLemmas.

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

    Lemma reserve_ratio_gt_0 :
        forall stableCoinState : StableCoinState,
            reserve_ratio (stableCoinState) > 0.
    Proof.
        intros. unfold reserve_ratio. apply Rdiv_pos_pos.
        - lra.
        - apply fusion_ratio_gt_0.  
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

    Lemma reserve_ratio_gt_1 :
        forall stableCoinState : StableCoinState,
            reserve_ratio (stableCoinState) > 1.
    Proof.
        intros. unfold reserve_ratio. apply division_greater_than_one.
        - apply fusion_ratio_lt_1.
        - apply fusion_ratio_gt_0.
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


    Lemma net_volume_lt_basecoins :
        forall (decay_event : Event) (state : State) (lastTimestamp : nat),
            Rabs (net_volume (decay_event) (state.(reactions)) (state.(stableCoinState)) (lastTimestamp)) < state.(stableCoinState).(reactorState).(baseCoins).
    Proof.
    Admitted.


    Lemma beta_decay_pos_fee_lt_1 :
        forall (decay_event : Event) (state : State) (lastTimestamp : nat),
            beta_decay_pos_fee (decay_event) (state.(reactions)) (state.(stableCoinState)) (lastTimestamp) < 1.
    Proof.
        intros. assert 
        (net_volume (decay_event) (state.(reactions)) (state.(stableCoinState)) (lastTimestamp) < (state.(stableCoinState).(reactorState).(baseCoins))) as H.
        {  apply abs_lt_implies_lt. apply net_volume_lt_basecoins. }
        destruct state. destruct stableCoinState0. destruct reactorState0.
        unfold beta_decay_pos_fee. simpl. simpl in H. unfold Rmax. destruct Rle_dec.
        - unfold Rdiv. rewrite Rmult_0_l. rewrite Rmult_0_r. rewrite Rplus_0_r.
        destruct betaDecayFee_assumption as [H1 H2].
        apply a_lt_c_strict with (b := extract_value betaDecayFee1).
            * destruct betaDecayFee0. simpl. nra.
            * destruct betaDecayFee1. simpl. nra.
            * apply H2.
        - apply Rlt_le_trans with (r2 := extract_value betaDecayFee0 + extract_value betaDecayFee1).
            * apply Rplus_lt_compat_l with (r := extract_value betaDecayFee0).
            rewrite <- Rmult_1_r. apply Rmult_lt_compat_l with (r := extract_value betaDecayFee1).
            destruct betaDecayFee1. simpl. apply r. unfold Rdiv.
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

    Lemma beta_decay_pos_fee_gt_0 :
        forall (decay_event : Event) (state : State) (lastTimestamp : nat),
            beta_decay_pos_fee (decay_event) (state.(reactions)) (state.(stableCoinState)) (lastTimestamp) > 0.
    Proof.
        intros. assert 
        (net_volume (decay_event) (state.(reactions)) (state.(stableCoinState)) (lastTimestamp) < (state.(stableCoinState).(reactorState).(baseCoins))) as H.
        {  apply abs_lt_implies_lt. apply net_volume_lt_basecoins. }
        destruct state; destruct stableCoinState0; destruct reactorState0;
        unfold beta_decay_pos_fee; unfold Rmax; destruct Rle_dec; simpl.
        - unfold Rdiv; rewrite Rmult_0_l; rewrite Rmult_0_r; rewrite Rplus_0_r; destruct betaDecayFee_assumption as [H1 H2].
            * destruct betaDecayFee0; simpl; nra.
        - apply Rplus_pos_pos.
            * destruct betaDecayFee0; simpl; nra.
            * apply Rmult_pos_pos.
                + destruct betaDecayFee1; simpl; nra.
                + apply Rdiv_pos_pos.
                    { simpl in n; nra. }
                    { apply basecoin_assumption. }
    Qed.

    Lemma beta_decay_neg_fee_gt_0 :
        forall (decay_event : Event) (state : State) (lastTimestamp : nat),
            beta_decay_neg_fee (decay_event) (state.(reactions)) (state.(stableCoinState)) (lastTimestamp) > 0.
    Proof.
        intros. assert 
        (net_volume (decay_event) (state.(reactions)) (state.(stableCoinState)) (lastTimestamp) < (state.(stableCoinState).(reactorState).(baseCoins))) as H.
        {  apply abs_lt_implies_lt. apply net_volume_lt_basecoins. }
        destruct state; destruct stableCoinState0; destruct reactorState0;
        unfold beta_decay_neg_fee; unfold Rmax; destruct Rle_dec; simpl.
        - unfold Rdiv; rewrite Rmult_0_l; rewrite Rmult_0_r; rewrite Rplus_0_r; destruct betaDecayFee_assumption as [H1 H2].
            * destruct betaDecayFee0; simpl; nra.
        - apply Rplus_pos_pos.
            * destruct betaDecayFee0; simpl; nra.
            * apply Rmult_pos_pos.
                + destruct betaDecayFee1; simpl; nra.
                + apply Rdiv_pos_pos.
                    { simpl in n; nra. }
                    { apply basecoin_assumption. }
    Qed.

    Lemma beta_decay_neg_fee_lt_1 :
        forall (decay_event : Event) (state : State) (lastTimestamp : nat),
            beta_decay_neg_fee (decay_event) (state.(reactions)) (state.(stableCoinState)) (lastTimestamp) < 1.
    Proof.
        intros. assert 
        (net_volume (decay_event) (state.(reactions)) (state.(stableCoinState)) (lastTimestamp) < (state.(stableCoinState).(reactorState).(baseCoins)) /\ -(state.(stableCoinState).(reactorState).(baseCoins)) < net_volume (decay_event) (state.(reactions)) (state.(stableCoinState)) (lastTimestamp)) as H.
        { 
            apply Rabs_def2. apply net_volume_lt_basecoins.
        }
        destruct state. destruct stableCoinState0. destruct reactorState0.
        unfold beta_decay_neg_fee. simpl. simpl in H. unfold Rmax. destruct Rle_dec.
        - unfold Rdiv. rewrite Rmult_0_l. rewrite Rmult_0_r. rewrite Rplus_0_r.
        destruct betaDecayFee_assumption as [H1 H2].
        apply a_lt_c_strict with (b := extract_value betaDecayFee1).
            * destruct betaDecayFee0. simpl. nra.
            * destruct betaDecayFee1. simpl. nra.
            * apply H2.
        - apply Rlt_le_trans with (r2 := extract_value betaDecayFee0 + extract_value betaDecayFee1).
            * apply Rplus_lt_compat_l with (r := extract_value betaDecayFee0).
            rewrite <- Rmult_1_r. apply Rmult_lt_compat_l.
            destruct betaDecayFee1. simpl. apply r. unfold Rdiv.
            apply Rmult_lt_reg_r with (r := baseCoins0).
                + destruct reactorstate_assumption with 
                (b := baseCoins0) (r := reserveCoins0) (s := stableCoins0) 
                as [H1 [H2 H3]]. apply H1.
                + rewrite Rmult_assoc. rewrite Rinv_l. rewrite Rmult_1_r.
                rewrite Rmult_1_l. simpl in H. destruct reactorstate_assumption with 
                (b := baseCoins0) (r := reserveCoins0) (s := stableCoins0) 
                as [H1 [H2 H3]]. unfold not. intros. nra. apply Rgt_not_eq. apply basecoin_assumption.
            * destruct betaDecayFee_assumption as [H1 H2]. apply H2.
    Qed.
        
    

    Lemma fusion_ratio_div_stablecoin_price :
        forall (sCS : StableCoinState),
            fusion_ratio (sCS) / stablecoin_price (sCS) = get_stablecoins (sCS.(reactorState)) / get_basecoins (sCS.(reactorState)).
    Proof.
        intros. unfold stablecoin_price. rewrite a_div_b_c_imp_a_mult_c_div_b.
        apply a_mult_b_div_a_mult_c_imp_b_div_c. apply Rgt_not_eq. 
        apply fusion_ratio_gt_0.
    Qed.

    Lemma fusion_ratio_div_reservecoin_price :
        forall (sCS : StableCoinState),
            (1 - fusion_ratio (sCS)) / reservecoin_price (sCS) = get_reservecoins (sCS.(reactorState)) / get_basecoins (sCS.(reactorState)).
    Proof.
        intros. unfold reservecoin_price. rewrite a_div_b_c_imp_a_mult_c_div_b.
        apply a_mult_b_div_a_mult_c_imp_b_div_c. apply Rgt_not_eq.
        apply Rgt_minus. apply fusion_ratio_lt_1.
    Qed.


    Lemma fission_output_alt :
        forall (sCS : StableCoinState) (bC : BaseCoins),
            fission_output (bC) (sCS) = 
            (
                (bC * (1 - extract_value (fissionFee)) * (get_stablecoins (sCS.(reactorState)))) / (get_basecoins (sCS.(reactorState))), 
                (bC * (1 - extract_value (fissionFee)) * (get_reservecoins (sCS.(reactorState)))) / (get_basecoins (sCS.(reactorState)))
            ).
    Proof.
        intros. unfold fission_output. 
        rewrite Rmult_assoc with 
        (r1 := bC) (r2 := fusion_ratio sCS) 
        (r3 := 1 - extract_value fissionFee).
        rewrite Rmult_assoc with 
        (r1 := bC) (r2 := 1 - fusion_ratio sCS) 
        (r3 := 1 - extract_value fissionFee).
        rewrite Rmult_comm with
        (r1 := fusion_ratio sCS) (r2 := 1 - extract_value fissionFee).
        rewrite Rmult_comm with
        (r1 := 1 - fusion_ratio sCS) (r2 := 1 - extract_value fissionFee).
        rewrite <- Rmult_assoc with 
        (r1 := bC) (r3 := fusion_ratio sCS) 
        (r2 := 1 - extract_value fissionFee).
        rewrite <- Rmult_assoc with 
        (r1 := bC) (r3 := 1 - fusion_ratio sCS) 
        (r2 := 1 - extract_value fissionFee).
        rewrite <- Rmult_div_assoc with
        (r1 := bC * (1 - extract_value fissionFee)) (r2 := fusion_ratio sCS)
        (r3 := stablecoin_price sCS).
        rewrite <- Rmult_div_assoc with
        (r1 := bC * (1 - extract_value fissionFee)) (r2 := 1 - fusion_ratio sCS)
        (r3 := reservecoin_price sCS).
        rewrite fusion_ratio_div_stablecoin_price.
        rewrite fusion_ratio_div_reservecoin_price.
        rewrite <- Rmult_div_assoc with
        (r1 := bC * (1 - extract_value fissionFee)) (r2 := get_reservecoins (reactorState sCS)).
        rewrite <- Rmult_div_assoc with
        (r1 := bC * (1 - extract_value fissionFee)) (r2 := get_stablecoins (reactorState sCS)).
        reflexivity.
    Qed.

    Lemma beta_decay_pos_output_alt :
        forall (rC : ReserveCoins) (fee : R) (sCS : StableCoinState),
            beta_decay_pos_output (rC) (fee) (sCS) = 
            (rC * (1 - fee) * (1 - fusion_ratio (sCS)) * get_stablecoins (sCS.(reactorState))) / (fusion_ratio (sCS) * get_reservecoins (sCS.(reactorState))).
    Proof.
        intros. unfold beta_decay_pos_output.
        destruct sCS as [[oldBC oldSC oldRC] oldER] eqn:Heqn.
        rewrite <- Heqn.
        pose proof reactorstate_assumption (oldBC) (oldRC) (oldSC) as [H1 [H2 H3]].
        pose proof fusion_ratio_gt_0 (sCS) as H4.  
        unfold reservecoin_price. unfold stablecoin_price. rewrite Heqn.
        field_simplify.
        - reflexivity.
        - split.
            + simpl. nra.
            + simpl. rewrite <- Heqn. nra.
        - simpl. split.
            + nra.
            + split.
                * nra.
                * split.
                    { nra. }
                    { rewrite <- Heqn. nra. }
    Qed.

    Lemma beta_decay_neg_output_alt :
        forall (sC : StableCoins) (fee : R) (sCS : StableCoinState),
            beta_decay_neg_output (sC) (fee) (sCS) = 
            (sC * (1 - fee) * (fusion_ratio (sCS)) * get_reservecoins (sCS.(reactorState))) / ((1 - fusion_ratio (sCS)) * get_stablecoins (sCS.(reactorState))).
    Proof.
        intros. unfold beta_decay_neg_output.
        destruct sCS as [[oldBC oldSC oldRC] oldER] eqn:Heqn.
        rewrite <- Heqn.
        pose proof reactorstate_assumption (oldBC) (oldRC) (oldSC) as [H1 [H2 H3]].
        pose proof fusion_ratio_lt_1 (sCS) as H4.  
        unfold stablecoin_price. unfold reservecoin_price. rewrite Heqn.
        field_simplify.
        - reflexivity.
        - split.
            + simpl. nra.
            + simpl. rewrite <- Heqn. nra.
        - simpl. split.
            + nra.
            + split.
                * nra.
                * split.
                    { nra. }
                    { rewrite <- Heqn. nra. }
    Qed.
            
    Lemma base_coins_for_n_stable_coins_correctness : 
    forall
        (state_0 state_1 : State) 
        (timestamp : nat) 
        (stablecoinsRequired : R)
        (fracProtonsDecay : R)
        (fracPosRangeProof : 0 < fracProtonsDecay < 1)
        (betaDecayPosFeeVal : R)
        (betaDecayPosFeeValRangeProof : 0 < betaDecayPosFeeVal < 1),
    stablecoins_from_m_basecoins (state_0) (timestamp) (state_1) 
    (
        base_coins_for_n_stable_coins (state_0) (timestamp) (state_1) 
        (stablecoinsRequired) (betaDecayPosFeeVal) (fracProtonsDecay)
    ) (betaDecayPosFeeVal) (fracProtonsDecay) = stablecoinsRequired.
    Proof.
        intros. 
        (* Unfolding definitions *)
        unfold base_coins_for_n_stable_coins. 
        unfold stablecoins_from_m_basecoins. unfold beta_decay_pos_output. 
        unfold fission_output.
        (* Substituting simple variables *)
        set (r := (reservecoin_price (stableCoinState state_0))).
        set (s' := stablecoin_price (stableCoinState state_1)).
        set (s := stablecoin_price (stableCoinState state_0)).
        set (N := stablecoinsRequired).
        set (q := fusion_ratio (stableCoinState state_0)).
        set (fiss := extract_value fissionFee).
        set (r' := reservecoin_price (stableCoinState state_1)).
        set 
        (
            b := r * s' * s * N / (q * (1 - fiss) * r * s' + (1 - q) * 
            fracProtonsDecay * (1 - fiss) * (1 - betaDecayPosFeeVal) *
            r' * s)
        ).
        rewrite <- Rmult_div_assoc with (r2 := 1 - fiss).
        rewrite Rmult_assoc with (r2 := q).
        assert (b * (1 - q) * (1 - fiss) /
        r * fracProtonsDecay * (1 - betaDecayPosFeeVal) *
        r' / s' = b * (1 - q) * (1 - fiss) /
        r * (fracProtonsDecay * (1 - betaDecayPosFeeVal) *
        r') / s') as H.
        { lra. } rewrite H. rewrite <- Rmult_div_swap with (r3 := r). simpl.
        rewrite <- Rdiv_mult_distr with (r2 := r).
        assert (b * (1 - q) * (1 - fiss) *
        (fracProtonsDecay * (1 - betaDecayPosFeeVal) * r') /
        (r * s') = b * (((1 - q) * (1 - fiss) * fracProtonsDecay * (1 - betaDecayPosFeeVal) * r') / (r * s'))) as H1.
        { nra. } rewrite H1.
        rewrite <- Rmult_plus_distr_l with (r1 := b).
        assert (q * ((1 - fiss) / s) = q * (1 - fiss) / s) as H2.
        { nra. } rewrite H2.
        rewrite add_frac_real with (b := s) (d := r * s').
        rewrite Rmult_assoc with (r3 := fracProtonsDecay).
        rewrite Rmult_comm with (r1 := 1 - fiss).
        rewrite <- Rmult_assoc with (r3 := 1 - fiss).
        rewrite <- Rmult_assoc with (r3 := s').
        unfold b.
        set (denom := q * (1 - fiss) * r * s' +
        (1 - q) * fracProtonsDecay *
        (1 - fiss) * (1 - betaDecayPosFeeVal) *
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
                * apply Rgt_minus. unfold fiss. destruct fissionFee.
                simpl. destruct a. apply r1.
                * unfold r. apply reservecoin_price_gt_0.
                * unfold s'. apply stablecoin_price_gt_0.
            - apply Rle_ge. apply Rmult_le_pos. apply Rmult_le_pos. apply Rmult_le_pos.
            apply Rmult_le_pos. apply Rmult_le_pos.
                * apply Rge_le. apply Rge_minus. apply Rgt_ge. apply Rlt_gt.
                unfold f. apply fusion_ratio_lt_1.
                * apply Rlt_le. destruct fracPosRangeProof. apply H3.
                * apply Rge_le. apply Rge_minus. apply Rgt_ge. apply Rlt_gt.
                unfold fiss. destruct fissionFee. simpl. destruct a. apply r1.
                * apply Rge_le. apply Rge_minus. apply Rgt_ge. apply Rlt_gt.
                destruct betaDecayPosFeeValRangeProof. apply H4.
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
     * If fusion ratio is pegged then the stablecoin price equals the target 
     * price.
     *)
    Lemma fusion_ratio_pegged_stablecoin_price_equals_target_price :
    forall 
        (stableCoinState : StableCoinState)
        (s e b : R),
        s = get_stablecoins (stableCoinState.(reactorState)) ->
        e = target_price (stableCoinState) ->
        b = get_basecoins (stableCoinState.(reactorState)) ->
        fusion_ratio (stableCoinState) = (s * e) / b ->
        stablecoin_price (stableCoinState) = target_price (stableCoinState).
    Proof.
        intros. unfold stablecoin_price. unfold target_price.
        rewrite <- H. unfold target_price in H0. rewrite <- H0. 
        rewrite <- H1. rewrite H2. field_simplify.
        - reflexivity.
        - split.
            + apply Rgt_not_eq. apply stablecoin_assumption.
            + apply Rgt_not_eq. apply basecoin_assumption.
    Qed.

    (*
     * If reserve ratio > 1/q* then fusion ratio is pegged
     *)
    Lemma reserve_ratio_gt_q_star_fusion_ratio_pegged :
    forall 
        (stableCoinState : StableCoinState)
        (s e b : R),
        s = get_stablecoins (stableCoinState.(reactorState)) ->
        e = get_exchange_rate (stableCoinState) ->
        b = get_basecoins (stableCoinState.(reactorState)) ->
        reserve_ratio (stableCoinState) > /extract_value qStar ->
        fusion_ratio (stableCoinState) = (s * e) / b.
    Proof.
        intros. unfold reserve_ratio in H2.
        apply Rinv_0_lt_contravar with (r1 := /extract_value qStar) in H2.
        rewrite Rdiv_1_l in H2. repeat rewrite Rinv_inv in H2.
        unfold fusion_ratio in H2.
        apply rmin_ab_lt_a_imp_b in H2.
        - unfold fusion_ratio. subst. apply H2.
        - destruct qStar as [qs Hqs]. simpl. apply Rinv_0_lt_compat. nra.
    Qed.

    (*
     * If I start in a pegged state and perform a fission reaction I will stay
     * in a pegged state.
     *)
    Lemma fission_reaction_preserves_pegged_state :
    forall 
        (state0 state1 : State)
        (timestamp : nat)
        (m : R)
        (sC0 eR0 bC0 sC1 eR1 bC1 : R),
        m > 0 ->
        sC0 = get_stablecoins (state0.(stableCoinState).(reactorState)) ->
        eR0 = get_exchange_rate (state0.(stableCoinState)) ->
        bC0 = get_basecoins (state0.(stableCoinState).(reactorState)) ->
        sC1 = get_stablecoins (state1.(stableCoinState).(reactorState)) ->
        eR1 = get_exchange_rate (state1.(stableCoinState)) ->
        bC1 = get_basecoins (state1.(stableCoinState).(reactorState)) ->
        fusion_ratio (state0.(stableCoinState)) = (sC0 * eR0) / bC0 ->
        state1 = execute (state0) (FissionEvent (m)) (timestamp) ->
        fusion_ratio (state1.(stableCoinState)) = (sC1 * eR1) / bC1.
    Proof.
        (* Rewriting and simplifying the goal *)
        intros; unfold fusion_ratio; rewrite <- H3; rewrite <- H4; rewrite <- H5.
        (* Transforming goal into sC1 * eR1 / bC1 < qStar *)
        apply Rmin_right; apply Rlt_le.
        (* Applying transitivity and generating 2 subgoals
         * 1. sC1 * eR1 / bC1 < sC0 * eR0 / bC0
         * 2. sC0 * eR0 / bC0 <= qStar
         *)
        apply Rlt_le_trans with (r2 := (sC0 * eR0) / bC0).
        (* Proving the first subgoal by showing:
         * 1. sC1 * eR1 / bC1 = ((sC0 * eR0) / bC0) * ((bC0 + m*(1-fissionFee)) / (bC0 + m))
         * 2. showing that (bC0 + m*(1-fissionFee)) / (bC0 + m) < 1
         * TODO: How to simplify the proofs after field_simplify?
         *)
        (* Proving 1*)
        - assert (sC1 * eR1 / bC1 = (sC0 * eR0 / bC0) * ((bC0 + m * (1 - extract_value fissionFee)) / (bC0 + m))) as H8.
          { 
            unfold execute in H7; unfold fission_reaction in H7; 
            unfold fission_output in H7; unfold stablecoin_price in H7; 
            rewrite H6 in H7; rewrite <- H0 in H7; rewrite <- H1 in H7; rewrite <- H2 in H7; 
            rewrite H7 in H3; rewrite H7 in H4; rewrite H7 in H5; simpl in H3; 
            simpl in H4; simpl in H5; rewrite H3; rewrite H4; rewrite H5; simpl;
            field_simplify.
            - reflexivity.
            - split. 
                + apply Rgt_not_eq. apply Rplus_pos_pos. 
                    * apply basecoin_assumption.
                    * apply H.
                + apply Rgt_not_eq. apply basecoin_assumption.
            - split.
                + apply Rgt_not_eq. apply basecoin_assumption.
                + repeat split.
                    * apply Rgt_not_eq. apply stablecoin_assumption.
                    * apply Rgt_not_eq. apply exchangerate_assumption.
                    * apply Rgt_not_eq. apply Rplus_pos_pos. 
                        -- apply basecoin_assumption.
                        -- apply H.
          }
          (* Proving 2 *)
          assert ((bC0 + m * (1 - extract_value fissionFee)) / (bC0 + m) < 1) as H9.
          {
            apply division_less_than_one. 
            - apply Rplus_lt_compat_l. rewrite <- Rmult_1_r. 
            apply Rmult_lt_compat_l.
                + apply basecoin_assumption.
                + destruct fissionFee. simpl. lra.
            - apply Rplus_pos_pos; apply basecoin_assumption.
          }
          (* Tying the proofs together *)
          rewrite H8; rewrite <- Rmult_1_r; apply Rmult_lt_compat_l.
          + apply Rdiv_pos_pos.
            * apply Rmult_pos_pos; try apply stablecoin_assumption; try apply exchangerate_assumption.
            * apply basecoin_assumption.
          + apply H9.
        (* Proving the second subgoal by showing that sC0 * eR0 / bC0 <= qStar *)
        - apply rmin_a_b_eq_b_imp_b_le_a; unfold fusion_ratio in H6;
        rewrite <- H0 in H6; rewrite <- H1 in H6; rewrite <- H2 in H6; apply H6.
    Qed.

    Lemma actual_price_le_target_price_neutron :
  	forall 
		(sCS : StableCoinState),
    stablecoin_price (sCS) <= target_price (sCS).
	Proof.
		intros [ [bC sC rC] eX ].
		unfold stablecoin_price, target_price, fusion_ratio, Rmin.
		destruct qStar as [qS HqS]; simpl.
		assert (bC > 0) by apply basecoin_assumption.
		assert (sC > 0) by apply stablecoin_assumption.
		destruct (Rle_dec qS (sC * eX / bC)) as [Hle | Hgt].
		- (* Pegged state: qS <= sC * eX / bC *)
		apply Rmult_le_compat_r with (r := bC) in Hle; [| lra ].
		unfold Rdiv in Hle. rewrite Rmult_assoc in Hle.
		rewrite Rinv_l in Hle; [| lra].
		rewrite Rmult_1_r in Hle.
		apply Rmult_le_compat_r with (r := / sC) in Hle; [| apply Rlt_le, Rinv_0_lt_compat; lra ].
		rewrite Rmult_assoc with (r1 := sC) (r2 := eX) in Hle.
		rewrite Rmult_comm with (r1 := eX) in Hle.
		rewrite <- Rmult_assoc in Hle.
		rewrite Rinv_r in Hle; [| lra].
		rewrite Rmult_1_l in Hle.
		exact Hle.
		- (* Non-pegged state: qS > sC * eX / bC, so price is target price *)
		unfold Rdiv. rewrite Rmult_assoc with (r1 := sC * eX). 
		rewrite Rinv_l; [| lra]. rewrite Rmult_1_r. 
		rewrite Rmult_comm with (r1 := sC * eX). rewrite <- Rmult_assoc. 
		rewrite Rinv_l; [| lra]. rewrite Rmult_1_l. apply Rle_refl.
	Qed.
End FunctionProofs.