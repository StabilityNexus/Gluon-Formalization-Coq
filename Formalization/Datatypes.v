(*
 * Importing the Libraries
 *)
Require Import Coq.Reals.Reals.
Require Import Floats.

 
(*
 * IMPORTANT
 * weight is interpreted as float
 * reads and writes : float
 *)

Definition StableCoins : Type := float.
Definition ReserveCoins : Type := float.
Definition BaseCoins : Type := float.
Definition ExchangeRate : Type := float.

Definition QStar : Type := {x : float | (ltb x 1) = true}.
Definition FissionFee : Type := {x : float | ((ltb 0 x) = true) /\ ((leb x 1) = true)}.
Definition FusionFee : Type := {x : float | ((ltb 0 x) = true) /\ ((leb x 1) = true)}.
Definition BetaDecayFee0 : Type := {x : float | (ltb 0 x) = true}.
Definition BetaDecayFee1 : Type := {x : float | (ltb 0 x) = true}.


Record ReactorState :=
{
    nuclei : BaseCoins;
    neutrons : StableCoins;
    protons : ReserveCoins;
}.

Record StableCoinParameters :=
{
    qStar : QStar;
    fissionFee : FissionFee;
    fusionFee : FusionFee;
    betaDecayFee0 : BetaDecayFee0;
    betaDecayFee1 : BetaDecayFee1; 
}. 

Record State :=
{
    reactorState : ReactorState;
    contractParameters : StableCoinParameters;
}.


    


