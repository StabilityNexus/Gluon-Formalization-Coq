(*
 * Importing the Libraries
 *)
Require Export List.
Require Export Reals.
From StableCoinFormalization Require Export HelperFunctions.

Module Datatypes.
    Import HelperFunctions. 
    Import Reals.

    Local Open Scope R_scope.

    Definition PosR : Type := {x : R | 0 < x}.
    Definition NonNegR : Type := {x : R | 0 <= x}.
    Definition FractionR : Type := {x : R | 0 <= x <= 1}.

    Definition StableCoins : Type := R.
    Definition ReserveCoins : Type := R.
    Definition BaseCoins : Type := R.
    Definition ExchangeRate : Type := R.
    
    Definition QStar : Type := {x : R | 0 < x < 1}.
    Definition FissionFee : Type := {x : R | 0 < x < 1}.
    Definition FusionFee : Type := {x : R | 0 < x < 1}.
    (*
     * + Beta Decay = transmute to neutron
     * - Beta Decay = transmute to proton
     *)
    Definition BetaDecayFee0 : Type := {x : R | 0 < x}.
    Definition BetaDecayFee1 : Type := {x : R | 0 < x}.
    Definition TimePeriod : Type := nat.
    Definition Timestamp : Type := nat.
    
    
    Record ReactorState :=
    {
        baseCoins : BaseCoins;
        stableCoins : StableCoins;
        reserveCoins : ReserveCoins;
    }.

    Definition get_basecoins (reactorState : ReactorState) : R :=
        reactorState.(baseCoins).
    
    Definition get_stablecoins (reactorState : ReactorState) : R :=
        reactorState.(stableCoins).
    
    Definition get_reservecoins (reactorState : ReactorState) : R :=
        reactorState.(reserveCoins).

    Inductive Event : Type :=
    | FissionEvent (baseCoins : BaseCoins)
    | FusionEvent (baseCoins : BaseCoins)
    | BetaDecayPosEvent (reserveCoins : ReserveCoins)
    | BetaDecayNegEvent (stableCoins : StableCoins).


    Record StableCoinState :=
    {
        reactorState : ReactorState;
        exchangeRate : ExchangeRate;
    }.

    Definition get_exchange_rate 
    (stableCoinState : StableCoinState) : R :=
        stableCoinState.(exchangeRate).

    (*
     * Timestamp: timestamp of the reaction
     * StableCoinState: state of the stablecoin contract before the reaction
                        state stored for convenience to easily calculate the 
                        volume of beta + and beta - reactions
     *)

    Definition Trace : Type := list (StableCoinState * Timestamp * Event).

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

    Inductive Choice : Type :=
    | Primary
    | Secondary.

    Record Offer :=
    {
        action : Action;
        choice : Choice;
        value : BaseCoins;
    }.
End Datatypes.




    


