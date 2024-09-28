From StableCoinFormalization Require Export Datatypes.
From StableCoinFormalization Require Export HelperFunctions.
From StableCoinFormalization Require Export Functions.
Require Export Lqa.


Lemma nonnegative_plus_nonnegative : 
    forall a b : Q,
        0 <= a -> 0 <= b -> 0 <= a + b.
Proof.
    intros a b Ha Hb.
    apply Qplus_le_compat with (x:=0) (z:=0) (y:=a) (t:=b). 
    - apply Ha.
    - apply Hb.
Qed.



Lemma denominator_small_implies_fraction_big :
    forall a b c : Q,
        0 <= a -> 0 <= b -> 0 < c -> a / (b + c) <= a / c.
Proof.
    intros.
    assert (H2: a * c <= a * (b + c)).
    - nra.
    - apply Qmult_le_compat_r with (z:=(/c)) in H2. 
    rewrite <- Qmult_assoc in H2. rewrite Qmult_inv_r in H2. 
    rewrite Qmult_1_r in H2.
    apply Qmult_le_compat_r with (z:=(/(b + c))) in H2. 
    rewrite <- Qmult_assoc in H2.
    assert (/ c * /(b + c) == /(b + c) * /c) as H3.
    { lra. } rewrite H3 in H2. rewrite <- Qmult_assoc in H2.
    assert ((b + c) * (/ (b + c) * / c) == (b + c) * / (b + c) * /c).
    { lra. } rewrite H4 in H2. rewrite Qmult_inv_r in H2.
    rewrite Qmult_1_l in H2.
        * unfold Qdiv. apply H2.
        * lra.
        * apply Qlt_le_weak. apply Qinv_lt_0_compat. lra.
        * lra.
        * apply Qlt_le_weak. apply Qinv_lt_0_compat. lra.
    Qed. 

    
