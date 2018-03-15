Require Import Coqlib.  
Require Import Maps. 

Require Import Integers.
Open Scope Z_scope.
Import ListNotations.

Set Asymmetric Patterns.

Require Import state. 
Require Import language.

Set Implicit Arguments.
Unset Strict Implicit.

Require Import logic.

Open Scope nat.
Open Scope code_scope.

(*+ soundness of instruction rule +*)
Definition ins_sound p q i :=
  forall s,
    s |= p -> (exists s', (Q__ s (cntrans i) s') /\ s' |= q).

(*+ soundness of instruction rule +*)
CoInductive safety : CodeHeap -> State -> Label -> Label -> asrt -> nat -> Prop :=
| safety_cons : forall C S pc npc q n,
    (
      forall S' i pc' npc',
        C pc = Some (cntrans i) ->
        P__ C (S, pc, npc) (S', pc', npc') ->
        safety C S' pc' npc' q n
    ) ->
    (
      forall S' pc' npc' aexp rd,
        C pc = Some (cjumpl aexp rd) ->
        P__ C (S, pc, npc) (S', pc', npc') ->
        safety C S' pc' npc' q n
    ) ->
    (
      forall S' pc' npc' aexp,
        C pc = Some (cbe aexp) ->
        P__ C (S, pc, npc) (S', pc', npc') ->
        safety C S' pc' npc' q n
    ) ->
    (
      forall S' pc' npc' aexp,
        C pc = Some (cbne aexp) ->
        P__ C (S, pc, npc) (S', pc', npc') ->
        safety C S' pc' npc' q n
    ) ->
    (
      forall f S1 S2 pc1 pc2 npc1 npc2,
        C pc = Some (ccall f) ->
        P__ C (S, pc, npc) (S1, pc1, npc1) ->
        P__ C (S1, pc1, npc1) (S2, pc2, npc2) ->
        safety C S2 pc2 npc2 q (Nat.succ n)
    ) ->
    (
      forall S1 S2 pc1 pc2 npc1 npc2,
        C pc = Some (cretl) ->
        P__ C (S, pc, npc) (S1, pc1, npc1) ->
        P__ C (S1, pc1, npc1) (S2, pc2, npc2) ->
        (
          (Nat.eqb n 0 = true /\ S2 |= q) \/
          (Nat.eqb n 0 = false /\ safety C S2 pc2 npc2 q (Nat.pred n))
        )
    ) ->
    safety C S pc npc q n.

Definition cdhp_subst (Spec Spec' : funspec) :=
  forall f fsp, Spec f = Some fsp -> Spec' f = Some fsp.

Definition cdhp_sound C Spec Spec' :=
  forall f1 f2 fp fq L S,
    Spec' (f1, f2) = Some (fp, fq) -> S |= (fp L) -> cdhp_subst Spec Spec' ->
    safety C S f1 f1 (fq L) 0.