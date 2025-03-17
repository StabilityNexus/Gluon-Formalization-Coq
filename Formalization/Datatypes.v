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

    (* Definition one_posq : PosQ.
    Proof.
        exists (1 # 1).
        unfold Qlt. simpl. lia.
    Defined.

    (* Function to multiply two PosQ values *)
    Definition mul_posq (a b : PosQ) : PosQ.
    Proof.
        (* Extract the rational numbers from a and b *)
        destruct a as [qa Ha].
        destruct b as [qb Hb].
        (* Multiply the two rational numbers *)
        exists (qa * qb).
        (* Prove that the product of two positive rationals is positive *)
        unfold Qlt in *.
        simpl. rewrite Zmult_1_r.
        apply Zmult_lt_0_compat. 
        - simpl in Ha. rewrite Zmult_1_r in Ha. assumption.
        - simpl in Hb. rewrite Zmult_1_r in Hb. assumption.
    Defined.

    Definition div_posq (a b : PosQ) : PosQ.
    Proof.
        (* Extract the rational numbers from a and b *)
        destruct a as [qa Ha].
        destruct b as [qb Hb].
        (* Divide the two rational numbers *)
        exists (qa / qb).
        (* Prove that the quotient of two positive rationals is positive *)
        unfold Qlt.
        simpl. rewrite Zmult_1_r.
        apply Z.lt_0_mul. left. split.
        - unfold Qlt in Ha. simpl in Ha. rewrite Zmult_1_r in Ha. apply Ha. 
        - assert (0 < / qb) as Hc. { apply Qinv_lt_0_compat. apply Hb. }
        unfold Qlt in Hc. simpl in Hc. rewrite Zmult_1_r in Hc. apply Hc.
    Defined.

    (* Function add two PosQ values *)
    Definition add_posq (a b : PosQ) : PosQ.
    Proof.
        (* Extract the rational numbers from a and b *)
        destruct a as [qa Ha].
        destruct b as [qb Hb].
        (* Multiply the two rational numbers *)
        exists (qa + qb).
        lra.
    Defined.

    (* Function to return the inverse of a PosQ value *)
    Definition inv_posq (a : PosQ) : PosQ.
    Proof.
    (* Extract the rational number from a *)
        destruct a as [qa Ha].
        (* The inverse of qa is 1 / qa *)
        exists (/ qa).
        (* Prove that the inverse is positive *)
        apply Qinv_lt_0_compat.
        assumption.
    Defined.

    (* Function to get the min of two PosQ values *)
    Definition min_posq 
        (a b : PosQ) (c : Q) 
        (H : extract_value (a) < c \/ extract_value (b) < c) 
        : {x : Q | 0 < x < c}.
    Proof.
        destruct a as [qa Ha].
        destruct b as [qb Hb]. simpl in H.
        exists (Qmin qa qb).
        split.
        - unfold Qmin. unfold Qcompare. unfold GenericMinMax.gmin. 
        destruct (Qnum qa * QDen qb ?= Qnum qb * QDen qa)%Z.
            * apply Ha.
            * apply Ha.
            * apply Hb.
        - apply Q.min_lt_iff. apply H.
    Defined.

    Definition sub_posq 
        (a b : PosQ) (H : extract_value (b) < extract_value (a)) : PosQ.
    Proof.
    (* Extract the rational number and its bounds *)
        destruct a as [qa Ha].
        destruct b as [qb Hb].
        simpl in H.
        (* We need to prove that 1 - qa is positive, i.e., 0 < 1 - qa *)
        exists (qa - qb). 
        nra. 
    Defined.

    (* Function to construct a PosQ from a QStar *)
    Definition qstar_to_posq (qstar : QStar) : PosQ.
        Proof.
        (* Destructure qstar to extract the rational number and the proof of 0 < qstar < 1 *)
        destruct qstar as [x [Hpos _]].
        (* Since 0 < x (from the hypothesis Hpos), we can construct PosQ *)
        exists x.
        (* The proof that 0 < x is already given by Hpos *)
        exact Hpos.
    Defined.

    (* Function to construct a PosQ from a QStar *)
    Definition fraction_to_posq (frac : Fraction) : PosQ.
        Proof.
        (* Destructure qstar to extract the rational number and the proof of 0 < qstar < 1 *)
        destruct frac as [x [Hpos _]].
        (* Since 0 < x (from the hypothesis Hpos), we can construct PosQ *)
        exists x.
        (* The proof that 0 < x is already given by Hpos *)
        exact Hpos.
    Defined.



    Theorem qstar_to_posq_lt_1 : 
        forall (a : QStar), extract_value (qstar_to_posq a) < 1.
    Proof.
        intros a.
        (* Destructure a to extract the rational number and its proof 0 < x < 1 *)
        destruct a as [x [Hgt0 Hlt1]].
        (* extract_value (qstar_to_posq a) = x, so we need to show x < 1 *)
        simpl.
        (* The proof that x < 1 is already given as Hlt1 *)
        exact Hlt1.
    Qed.

    Theorem a_lt_impl_a_lt_or_b_lt : 
        forall (a b : PosQ) (c : Q) (H : extract_value (a) < c),
        extract_value (a) < c \/ extract_value (b) < c.
    Proof.
        intros.
        left; apply H.
    Qed.

    Theorem qstar_lt_1 : 
        forall (a : QStar),
        extract_value (qstar_to_posq (a)) < extract_value (one_posq).
    Proof.
        intros.
        destruct a as [qa [H1 H2]]. simpl. apply H2.
    Qed.

    (* Define infix operators *)

    (* Multiplication operator *)
    Notation "a *p b" := (mul_posq a b) (at level 40, left associativity).

    (* Division operator *)
    Notation "a //p b" := (div_posq a b) (at level 40, left associativity).

    (* Addition operator *)
    Notation "a +p b" := (add_posq a b) (at level 50, left associativity).

    (* Inverse operator (unary operator for inverse) *)
    Notation "'/p' a" := (inv_posq a) (at level 35, right associativity). *)
End Datatypes.




    


