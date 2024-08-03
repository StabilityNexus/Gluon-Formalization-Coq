(*
 * Importing the Libraries
 *)
Require Export Coq.Reals.Reals.
Require Export Floats.
Require Export Coq.Floats.PrimFloat.
Require Export List.

Module Datatypes.
    Definition PositiveF : Type := {x : float | (ltb 0 x) = true}.
    Definition NonNegativeF : Type := {x : float | (leb 0 x) = true}.

    Definition StableCoins : Type := PositiveF.
    Definition ReserveCoins : Type := PositiveF.
    Definition BaseCoins : Type := NonNegativeF.
    Definition ExchangeRate : Type := PositiveF.
    
    Definition QStar : Type := {x : float | (ltb x 1) = true /\ (ltb 0 x) = true}.
    Definition FissionFee : Type := {x : float | (ltb 0 x) = true /\ (leb x 1) = true}.
    Definition FusionFee : Type := {x : float | (ltb 0 x) = true /\ (leb x 1) = true}.
    Definition BetaDecayFeePos : Type := PositiveF.
    Definition BetaDecayFeeNeg : Type := PositiveF.
    Definition TimePeriod : Type := nat.
    
    
    Record ReactorState :=
    {
        nuclei : BaseCoins;
        neutrons : StableCoins;
        protons : ReserveCoins;
    }.
    
    
    Inductive Reaction : Type :=
    | Fission (nuclei : PositiveF) (neutrons : PositiveF) (protons : PositiveF)
    | Fusion (neutrons : PositiveF) (protons : PositiveF) (nuclei : PositiveF)
    | BetaDecayPos (protons : PositiveF) (neutrons : PositiveF)
    | BetaDecayNeg (neutrons : PositiveF) (protons : PositiveF).

    Record StableCoinState :=
    {
        reactorState : ReactorState;
        exchangeRate : ExchangeRate;
    }.

    Definition Trace : Type := list (StableCoinState * Reaction).

    (*
     * The 'reactions' trace is ordered from MOST RECENT (stored at the head) 
     * to LEAST RECENT (stored at the end).
     *)
    Record State :=
    {
        stableCoinState : StableCoinState;
        reactions : Trace; 
    }.

    Inductive Action : Type :=
    | BuyStableCoin
    | SellStableCoin.

    Definition SecondaryMarketAction : Type := (Action * BaseCoins).
End Datatypes.




    


