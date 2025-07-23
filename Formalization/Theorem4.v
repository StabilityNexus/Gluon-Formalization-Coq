From StableCoinFormalization Require Export Datatypes.
From StableCoinFormalization Require Export HelperFunctions.
From StableCoinFormalization Require Export Functions.
From StableCoinFormalization Require Export HelperLemmas.
From StableCoinFormalization Require Export FunctionProofs.
Require Export Lia.
Local Open Scope R_scope.
Module Theorem4.
    Import Datatypes.
    Import HelperFunctions.
    Import HelperLemmas.
    Import FunctionProofs.
    Import Functions.
    Import Lia.
    Theorem insolvency :
        forall (s : State),
            equity (s.(stableCoinState)) >= 0.
    Proof.
        destruct s as [scs r]. destruct scs as [rs e]. 
        destruct rs as [bc sc rc]. unfold equity. simpl.
        left. apply Rmult_pos_pos. apply Rgt_minus. apply fusion_ratio_lt_1.
        destruct reactorstate_assumption with (b := bc) (r := rc) (s := sc) as [H1 [H2 H3]].
        apply H1.
    Qed.
End Theorem4.



