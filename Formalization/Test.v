Require Import List.

Definition var : Type := nat.

Inductive expr : Type :=
| ENat (n : nat)
| EVar (v : var)
| EAdd (e1 e2 : expr)
| EMult (e1 e2 : expr)
| ECond (e1 e2 e3 : expr).


Inductive program : Type :=
| PRes (e : expr)
| PLet (e : expr) (p : program).

Inductive wf_expr (max : var) : expr -> Prop :=
| WFNat : forall (n : nat), wf_expr (max) (ENat (n))
| WFVar : forall (v : var), v < max -> wf_expr (max) (EVar (v))
| WFAdd : forall (e1 e2 : expr), wf_expr (max) (e1) -> wf_expr (max) (e2) -> wf_expr (max) (EAdd (e1) (e2))
| WFMult : forall (e1 e2 : expr), wf_expr (max) (e1) -> wf_expr (max) (e2) -> wf_expr (max) (EMult (e1) (e2))
| WFCond : forall (e1 e2 e3 : expr), wf_expr (max) (e1) -> wf_expr (max) (e2) -> wf_expr (max) (e3) ->  wf_expr (max) (ECond (e1) (e2) (e3)).

Inductive wf_program' (max : var) : program -> Prop :=
| WFRes : forall (e : expr), wf_expr (max) (e) -> wf_program' (max) (PRes (e))
| WFLet : forall (e : expr) (p : program), wf_expr (max) (e) -> wf_program' (S (max)) (p) -> wf_program' (max) (PLet (e) (p)).

Definition wf_program := wf_program' 0.

Definition environment := list (nat).

Fixpoint eval_expr (env : environment) (e : expr) : option (nat) :=
    match e with
    | ENat (n) => Some (n)
    | EVar (v) => nth_error (env) (v)
    | EAdd (e1) (e2) =>
        match eval_expr (env) (e1), eval_expr (env) (e2) with
        | Some (res1), Some (res2) => Some (res1 + res2)
        | _, _ => None
        end
    | EMult (e1) (e2) =>
        match eval_expr (env) (e1), eval_expr (env) (e2) with
        | Some (res1), Some (res2) => Some (res1 * res2)
        | _, _ => None
        end
    | ECond (e1) (e2) (e3) =>
        match eval_expr (env) (e1) with
        | Some (0) => eval_expr (env) (e2)
        | Some (_) => eval_expr (env) (e3)
        | _ => None
        end
    end.

Fixpoint eval_program' (env: environment) (p: program) : option (nat) :=
    match p with
    | PLet e p' =>
        match eval_expr env e with
        | Some n => eval_program' (env ++ (n :: nil)) p'
        | None => None
        end
    | PRes e => eval_expr env e
    end.
    
Definition eval_program p := eval_program' nil p.

(* Theorems *)
Lemma wf_expr_eval :
  forall e env,
    wf_expr (length env) e ->
    exists n, eval_expr env e = Some n.
Proof.
    intros e env Hwf.
    induction Hwf; simpl; eauto; try solve [
        repeat (
            let n := fresh "n" in
            match goal with
            | H : exists n, _ = _ |- _ => destruct H as [n -> ]
            end
        ); eauto
    ].
    - apply nth_error_Some in H. destruct (nth_error env v) as [x | ]; [eauto | congruence].
    - destruct IHHwf1 as [x0 ->]. destruct IHHwf2 as [x1 ->]. destruct IHHwf3 as [x2 ->].
        match goal with
        | _ : _ |- context [match ?n with | _ => _ end] => destruct n
        end; eauto.
    Qed.
    

Lemma wf_program'_eval:
  forall env p,
    wf_program' (length env) p ->
    exists n, eval_program' env p = Some n.
Proof.
  intros env p Hwf.
  remember (length env).
  generalize dependent env.
  induction Hwf.
  - intros env Heq. subst.
    simpl. apply wf_expr_eval in H.
    destruct H.
    rewrite H.
    assert (Hlen: S (length env) = length (env ++ x :: nil)).
    {
      rewrite app_length. simpl. rewrite PeanoNat.Nat.add_1_r.
      reflexivity.
    }
    apply IHHwf in Hlen.
    destruct Hlen.
    exists x0. apply H0.
  - intros env Heq. subst.
    simpl. apply wf_expr_eval in H.
    apply H.
Qed.

Theorem wf_program_eval:
  forall p,
    wf_program p ->
    exists n, eval_program p = Some n.
Proof.
  intros p Hwf.
  apply wf_program'_eval.
  apply Hwf.
Qed.
    