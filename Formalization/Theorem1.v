From StableCoinFormalization Require Export Datatypes.
From StableCoinFormalization Require Export HelperFunctions.
From StableCoinFormalization Require Export Functions.

Module Theorem1.
    Import Datatypes.
    Import HelperFunctions.
    Import Functions.

    Theorem peg_maintenance_upper_bound :
        forall (state : StableCoinState) (secondaryMarketAction : SecondaryMarketAction) (baseCoins : BaseCoins) (effectiveFee : float),
            ltb (div (1) (extract_value (qStar))) (reserve_ratio (state)) = true /\
            secondaryMarketAction = (SellStableCoin, baseCoins) /\
            ltb (mul (add (1) (effectiveFee)) (target_price (state))) (extract_value (baseCoins)) = true
            ->
            (is_rational_choice (secondaryMarketAction) (state) = true -> False) /\
            (leb (effectiveFee) (sub (div (1) (mul (sub (1) (extract_value (fissionFee))) (sub (1) (extract_value (betaDecayFeePos))))) (1)) = true).
    
    Proof.
        intros. split. destruct H as [H1 [H2 H3]].
        - rewrite H2. simpl.
    
    
End Theorem1.



