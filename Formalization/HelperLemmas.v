Require Export Reals. 
Require Export Lra.
Local Open Scope R_scope.

Module HelperLemmas.
    Import Lra.
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

    Lemma a_lt_c_strict : 
        forall a b c : R, 0 < a -> 0 < b -> a + b <= c -> a < c.
    Proof.
        intros a b c Ha Hb Hsum.
        (* We know a + b <= c and 0 < b, so a must be strictly less than c *)
        apply Rlt_le_trans with (r2 := a + b).
        - nra.
        - apply Hsum. 
    Qed.

    Lemma abs_lt_implies_lt : forall a b : R, Rabs a < b -> a < b.
    Proof.
        intros a b HRabs.
        unfold Rabs in HRabs.
        destruct (Rcase_abs a) as [H_neg | H_nonneg].
        - nra.
        - nra.
    Qed.

    Lemma rmin_ab_lt_a_imp_b :
        forall (r1 r2 : R),
            Rmin (r1) (r2) < r1 -> Rmin (r1) (r2) = r2. 
    Proof.
        intros. unfold Rmin. unfold Rmin in H. destruct Rle_dec. 
        - nra.
        - reflexivity.
    Qed.

    Lemma a_div_b_c_imp_a_mult_c_div_b :
        forall (a b c : R),
            a / (b / c) = (a * c) / b.
    Proof.
        intros. unfold Rdiv. rewrite Rmult_comm with (r1 := b).
        rewrite Rinv_mult. rewrite Rinv_inv. rewrite Rmult_assoc.
        reflexivity. 
    Qed.

    Lemma a_mult_b_div_a_mult_c_imp_b_div_c :
        forall (a b c : R),
            a <> 0 -> (a * b) / (a * c) = b / c.
    Proof.
        intros. unfold Rdiv. rewrite Rinv_mult. rewrite Rmult_comm with (r1 := a) (r2 := b).
        rewrite Rmult_assoc with (r1 := b) (r2 := a). rewrite <- Rmult_assoc with (r1 := a) (r2 := / a).
        rewrite Rinv_r. rewrite Rmult_1_l.
        - reflexivity.
        - apply H.
    Qed.

    Lemma a_div_b_mult_c_div_d_imp_a_mult_c_div_b_mult_d :
        forall (a b c d : R),
            (a / b) * (c / d) = (a * c) / (b * d).
    Proof.
        intros. rewrite Rdiv_mult_distr with (r1 := a * c). nra.
    Qed.

    Lemma a_mult_b_div_a_eq_b :
        forall (a b : R),
            a <> 0 -> a * (b / a) = b.
    Proof.
        intros. unfold Rdiv. rewrite Rmult_comm with (r1 := b) (r2 := /a).
        rewrite <- Rmult_assoc. rewrite Rinv_r.
        - nra.
        - nra. 
    Qed.

    Lemma division_greater_than_one :
    forall (a b : R),
        a > b ->
        b > 0 ->
        a / b > 1.
    Proof.
        intros a b Hab Hb.
        unfold Rdiv.
        apply Rmult_gt_compat_r with (r := / b) in Hab.
        - field_simplify in Hab. lra. lra. lra.
        - apply Rinv_pos. apply Hb. 
    Qed.

    Lemma division_less_than_one :
    forall (a b : R),
        a < b ->
        b > 0 ->
        a / b < 1.
    Proof.
        intros a b Hab Hb.
        unfold Rdiv.
        apply Rmult_gt_compat_r with (r := / b) in Hab.
        - field_simplify in Hab. lra. lra. lra.
        - apply Rinv_pos. apply Hb. 
    Qed.

    Lemma a_div_b_mult_c_div_d_imp_a_mult_d_div_b_mult_c :
    forall (a b c d : R),
        a / (b * (c / d)) = (a * d) / (b * c).
    Proof.
        intros. rewrite Rmult_div_assoc with
        (r1 := b)
        (r2 := c)
        (r3 := d).
        rewrite a_div_b_c_imp_a_mult_c_div_b. reflexivity.
    Qed.

    Lemma a_ge_b_imp_a_mult_c_gt_b :
        forall (a b c : R),
            a > 0 -> c > 1 -> a >= b -> a * c > b.
    Proof.
        intros. destruct H1.
        - apply Rgt_trans with (r2 := a).
            + rewrite <- Rmult_1_r. apply Rmult_gt_compat_l.
                * nra.
                * nra.
            + nra.
        - rewrite H1. nra. 
    Qed.

    Lemma a_gt_b_imp_a_mult_c_gt_b :
        forall (a b c : R),
            a > 0 -> c > 1 -> a > b -> a * c > b.
    Proof.
        intros. apply Rgt_trans with (r2 := a).
        - rewrite <- Rmult_1_r. apply Rmult_gt_compat_l.
            + nra.
            + nra.
        - nra. 
    Qed.

    Lemma a_lt_b_imp_a_mult_c_lt_b :
        forall (a b c : R),
            a > 0 -> c < 1 -> a < b -> a * c < b.
    Proof.
        intros. apply Rgt_trans with (r2 := a).
        - nra.
        - rewrite <- Rmult_1_r with (r := a) at 1. apply Rmult_gt_compat_l. nra. nra.
    Qed.

    Lemma a_div_b_mult_c_lt_a_div_b :
        forall (a b c : R),
            a > 0 -> b > 0 -> c > 1 -> a / (b * c) < a / b.
    Proof.
        intros. unfold Rdiv.
        apply Rmult_lt_compat_l with (r := a).
        - apply H.
        - rewrite Rinv_mult. rewrite <- Rmult_1_r.
        apply Rmult_lt_compat_l with (r := /b). apply Rinv_pos. apply H0.
        rewrite <- Rinv_1. apply Rinv_0_lt_contravar. nra. apply H1.
    Qed.
End HelperLemmas.
