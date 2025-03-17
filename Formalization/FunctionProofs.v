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
            
    (* Theorem base_coins_for_n_stable_coins_correctness : 
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
    Qed.  *)
End FunctionProofs.