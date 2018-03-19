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

Ltac destruct_state s :=
  destruct s as [ [ ?m [?r ?f] ] ?d ].

(*+ Some tactic for Sep Proof +*)


Theorem lift_assert_stable :
  forall p s n,
    s |= p -> s |= lift_nth_asrt p n.
Proof.
  intro p.
  induction p; intros.

  - (* Aemp *)
    destruct n.
    simpl.
    exists 
    
  