Require Export Reals.
Module HelperFunctions.
    Import Reals.
    
    Definition extract_value {A : Type} {P : A -> Prop} (x : {a : A | P a}) : A :=
        proj1_sig x.
    
    Definition Rlt_b (a : R) (b : R) : bool :=
        if Rlt_dec (a) (b) then true else false.

    Definition Req_b (x y : R) : bool :=
        if Req_EM_T x y then true else false.
End HelperFunctions.




