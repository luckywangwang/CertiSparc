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
Fixpoint get_nth_asrt (a : asrt) (n : nat) : option asrt :=
  match n with
  | O => match a with
        | p ** q => Some p
        | _ => Some a
        end
  | S n' => match a with
           | p ** q => get_nth_asrt q n'
           | _ => None
           end
  end.

Fixpoint remove_nth_asrt (a : asrt) (n : nat) : asrt :=
  match n with
  | O => match a with
        | p ** q => q
        | _ => Aemp
        end
  | S n' => match a with
           | p ** q => p ** remove_nth_asrt q n'
           | _ => a
           end
  end.

Definition lift_nth_asrt (a : asrt) (n : nat) : asrt :=
  match get_nth_asrt a n with
  | Some p =>
    match remove_nth_asrt a n with
    | Aemp => p
    | q => p ** q
    end
  | _ => a
  end.

(* test *)


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
    
  