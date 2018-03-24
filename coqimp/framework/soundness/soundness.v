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

Inductive comtype := tc | ti | tj | tr | tbe | tbne.

Inductive steprecord :=
| step_end : steprecord
| step_cons : comtype -> steprecord -> steprecord.

Inductive safety_step : CodeHeap -> State -> Label -> Label -> asrt -> steprecord -> nat -> Prop :=
| safety_step_i :
    forall C S pc npc q n cls,
      (forall S' i pc' npc', 
        C pc = Some (cntrans i) ->
        P__ C (S, pc, npc) (S', pc', npc') ->
        safety_step C S' pc' npc' q cls n) ->
      safety_step C S pc npc q (step_cons ti cls) n

| safety_step_j :
    forall C S pc npc q n cls,
      (forall S1 S2 pc1 pc2 npc1 npc2 aexp rd,
        C pc = Some (cjumpl aexp rd) ->
        P__ C (S, pc, npc) (S1, pc1, npc1) ->
        P__ C (S1, pc1, npc1) (S2, pc2, npc2) ->
        safety_step C S2 pc2 npc2 q cls n) ->
      safety_step C S pc npc q (step_cons tj cls) n

| safety_step_be :
    forall C S pc npc q n cls,
      (forall S1 S2 pc1 pc2 npc1 npc2 aexp,
        C pc = Some (cbe aexp) ->
        P__ C (S, pc, npc) (S1, pc1, npc1) ->
        P__ C (S1, pc1, npc1) (S2, pc2, npc2) ->
        safety_step C S2 pc2 npc2 q cls n) ->
      safety_step C S pc npc q (step_cons tbe cls) n

| safety_step_bne :
    forall C S pc npc q n cls,
      (forall S1 S2 pc1 pc2 npc1 npc2 aexp,
        C pc = Some (cbne aexp) ->
        P__ C (S, pc, npc) (S1, pc1, npc1) ->
        P__ C (S1, pc1, npc1) (S2, pc2, npc2) ->
        safety_step C S2 pc2 npc2 q cls n) ->
      safety_step C S pc npc q (step_cons tbne cls) n

| safety_step_call :
    forall C S pc npc q n cls,
      (forall S1 S2 pc1 pc2 npc1 npc2 f,
        C pc = Some (ccall f) ->
        P__ C (S, pc, npc) (S1, pc1, npc1) ->
        P__ C (S1, pc1, npc1) (S2, pc2, npc2) ->
        safety_step C S2 pc2 npc2 q cls (Nat.succ n)) ->
      safety_step C S pc npc q (step_cons tc cls) n

| safety_step_ret1 :
    forall C S pc npc q,
      (forall S1 S2 pc1 pc2 npc1 npc2,
        C pc = Some (cretl) ->
        P__ C (S, pc, npc) (S1, pc1, npc1) ->
        P__ C (S1, pc1, npc1) (S2, pc2, npc2) -> S2 |= q) ->
      safety_step C S pc npc q (step_end) 0

| safety_step_ret2 :
    forall C S pc npc q n cls,
      (forall S1 S2 pc1 pc2 npc1 npc2,
        C pc = Some (cretl) -> n > 0 ->
        P__ C (S, pc, npc) (S1, pc1, npc1) ->
        P__ C (S1, pc1, npc1) (S2, pc2, npc2) ->
        safety_step C S2 pc2 npc2 q cls (Nat.pred n)) ->
      safety_step C S pc npc q (step_cons tr cls) n.        

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
    safety C S f1 f2 (fq L) 0.