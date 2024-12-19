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
End HelperLemmas.