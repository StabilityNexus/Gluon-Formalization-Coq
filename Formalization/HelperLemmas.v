Require Export Reals.
Local Open Scope R_scope.

Module HelperLemmas.
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
End HelperLemmas.