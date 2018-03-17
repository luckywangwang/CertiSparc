Require Import Coqlib.  
Require Import Maps.
Require Import LibTactics.

Require Import Integers.
Open Scope Z_scope. 
Import ListNotations.

Set Asymmetric Patterns.
 
Require Import state. 
Require Import language.

Set Implicit Arguments.
Unset Strict Implicit.
 
Require Import logic.
Require Import soundness.
 
Require Import lemmas.

Open Scope nat.
Open Scope code_scope.

(*+ Some tactic for Sep Proof +*)
Fixpoint asrt_to_lst (a : asrt) : list asrt :=
  match a with
  | p ** q => p :: asrt_to_lst q
  | _ => a :: nil
  end.

Fixpoint lst_to_asrt (ls : list asrt) : asrt :=
  match ls with
  | a :: nil => a
  | a :: ls' => a ** lst_to_asrt ls'
  | nil => Aemp
  end.

Fixpoint lift_n' {A : Type} (ls : list A) (n : nat) (prels : list A) :=
  match n with
  | S n' =>
    match ls with
    | a :: ls' => lift_n' ls' n' (prels ++ (a :: nil))
    | nil => prels ++ ls
    end
  | O =>
    match ls with
    | a :: ls' => a :: prels ++ ls'
    | nil => prels
    end
  end.

Definition lift_n {A : Type} (ls : list A) (n : nat) :=
  lift_n' ls n nil.

Lemma asrt_to_lst_nil_false :
  forall p,
    asrt_to_lst p = nil -> False.
Proof.
  intro p.
  induction p; intros;
    simpls; tryfalse.
Qed.
  
Lemma sep_lift_stable :
  forall p s ls n,
    s |= p -> asrt_to_lst p = ls ->
    s |= lst_to_asrt (lift_n ls n).
Proof.
  intro p.
  induction p; intros;
    try solve
      [
        simpls; subst; destruct n; simpl; eauto;
        unfold lift_n; simpl; destruct n; eauto
      ].

  -
    subst.
    destruct n0; simpl; eauto.
    unfold lift_n.
    simpl.
    destruct n0; eauto.

  -
    simpl in H0.
    destruct ls; tryfalse.
    inversion H0.
    subst.
    clear H0.
    simpl in H.
    simpljoin1.
    renames x to s1, x0 to s2.
    unfold lift_n.  
    simpl lift_n'.
    destruct n.
    { 
      simpl lst_to_asrt.
      destruct (asrt_to_lst p2) eqn:Heqe.
      {
        eapply asrt_to_lst_nil_false in Heqe; tryfalse.
      }
      {
        simpl sat.
        exists s1 s2.
        repeat (split; eauto).
        destruct l.
        eapply IHp2 with (ls := [a0]) (n := 0) in H1; eauto.
        eapply IHp2 with (ls := a0 :: a1 :: l) (n := 0) in H1; eauto.
      }
    }
    {
      
    }
  


