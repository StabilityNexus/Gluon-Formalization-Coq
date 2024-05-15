(*
 * Importing the Libraries
 *)
Require Import Coq.Reals.Reals.
Require Import Floats.
From StableCoinFormalization Require Export Datatypes.
From StableCoinFormalization Require Export HelperFunctions.


Definition target_price_stablecoin (exchangeRate : ExchangeRate) : BaseCoins :=
    exchangeRate.

Definition fusion_ratio (state : State) (exchangeRate : ExchangeRate) : float :=
    let
        qStarVal := 
        match (state.(contractParameters).(qStar)) with
        | exist _ x _ => x
        end
    in
        if eqb (state.(reactorState).(nuclei)) (0)
        then
            qStarVal
        else 
            float_min 
            (qStarVal)
            (div 
                (mul (state.(reactorState).(neutrons)) (exchangeRate)) 
                (qStarVal)).






