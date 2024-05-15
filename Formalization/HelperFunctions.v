Require Import Floats.


Definition float_min (x y : float) : float :=
    if (leb x y) 
    then x
    else y.

Definition float_max (x y : float) : float :=
    if (leb x y) 
    then y
    else x.



