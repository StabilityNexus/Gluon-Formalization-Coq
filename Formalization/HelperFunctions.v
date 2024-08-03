Require Export Floats.

Module HelperFunctions.
    Definition float_min (x y : float) : float :=
        if (leb x y) 
        then x
        else y.

    Definition float_max (x y : float) : float :=
        if (leb x y) 
        then y
        else x.
    
    Definition extract_value {A : Type} {P : A -> Prop} (x : {a : A | P a}) : A :=
        proj1_sig x.
End HelperFunctions.




