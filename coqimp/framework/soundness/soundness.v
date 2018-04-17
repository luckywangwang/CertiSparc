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

(*+ soundness of instruction sequence rule +*)
Inductive safety_insSeq : CodeHeap -> State -> Label -> Label -> asrt -> funspec -> Prop :=
| i_seq : forall C S pc npc q Spec i,
    C pc = Some (cntrans i) -> 
    (
      exists S' pc' npc',
        P__ C (S, pc, npc) (S', pc', npc')
    ) ->
    (
      forall S' pc' npc',
        P__ C (S, pc, npc) (S', pc', npc') ->
        safety_insSeq C S' pc' npc' q Spec
    ) ->
    safety_insSeq C S pc npc q Spec

| call_seq : forall C S pc npc q Spec f,
    C pc = Some (ccall f) ->
    (
      exists S1 S2 pc1 npc1 pc2 npc2,
        P__ C (S, pc, npc) (S1, pc1, npc1) /\
        P__ C (S1, pc1, npc1) (S2, pc2, npc2)
    ) ->
    (
      forall S1 S2 pc1 npc1 pc2 npc2,
        P__ C (S, pc, npc) (S1, pc1, npc1) ->
        P__ C (S1, pc1, npc1) (S2, pc2, npc2) ->
        (
          exists fp fq L r,
            pc2 = f /\ npc2 = f +ᵢ ($ 4) /\
            Spec (f, f +ᵢ ($ 4)) = Some (fp, fq) /\ S2 |= (fp L) ** r /\
            DlyFrameFree r /\
            (forall S', S' |= (fq L) ** r ->
                        safety_insSeq C S' (pc +ᵢ ($ 8)) (pc +ᵢ ($ 12)) q Spec) /\
            (forall S' S'', S' |= fp L -> S'' |= fq L ->
                            (get_R (getregs S') r15 = Some pc /\
                             get_R (getregs S'') r15 = Some pc))
        )
    ) ->
    safety_insSeq C S pc npc q Spec

| jmpl_seq : forall C S pc npc q aexp rd Spec,
    C pc = Some (cjumpl aexp rd) ->
    (
      exists S1 S2 pc1 npc1 pc2 npc2,
        P__ C (S, pc, npc) (S1, pc1, npc1) /\
        P__ C (S1, pc1, npc1) (S2, pc2, npc2)
    ) ->
    (
      forall S1 S2 pc1 npc1 pc2 npc2,
        P__ C (S, pc, npc) (S1, pc1, npc1) ->
        P__ C (S1, pc1, npc1) (S2, pc2, npc2) ->
        (
          exists fp fq L r,
            Spec (pc2, npc2) = Some (fp, fq) /\ S2 |= (fp L) ** r /\ (fq L) ** r ==> q /\
            DlyFrameFree r
        )
    ) ->
    safety_insSeq C S pc npc q Spec

| be_seq : forall C S pc npc q f Spec,
    C pc = Some (cbe f) ->
    (
      exists S1 S2 pc1 npc1 pc2 npc2,
        P__ C (S, pc, npc) (S1, pc1, npc1) /\
        P__ C (S1, pc1, npc1) (S2, pc2, npc2)
    ) ->
    (
      forall S1 S2 pc1 npc1 pc2 npc2,
        P__ C (S, pc, npc) (S1, pc1, npc1) ->
        P__ C (S1, pc1, npc1) (S2, pc2, npc2) ->
        (
          exists v, get_R (getregs S) z = Some v /\
          (
            v <> ($ 0) ->
            (
              exists fp fq L r,
                Spec (pc2, npc2) = Some (fp, fq) /\ S2 |= (fp L) ** r /\
                (fq L ** r) ==> q /\ DlyFrameFree r
            )
          ) /\
          ( 
            v = ($ 0) ->
            safety_insSeq C S2 pc2 npc2 q Spec
          )
        )
    ) ->
    safety_insSeq C S pc npc q Spec

| bne_seq : forall C S pc npc q f Spec,
    C pc = Some (cbne f) ->
    (
      exists S1 S2 pc1 npc1 pc2 npc2,
        P__ C (S, pc, npc) (S1, pc1, npc1) /\
        P__ C (S1, pc1, npc1) (S2, pc2, npc2)
    ) ->
    (
      forall S1 S2 pc1 npc1 pc2 npc2,
        P__ C (S, pc, npc) (S1, pc1, npc1) ->
        P__ C (S1, pc1, npc1) (S2, pc2, npc2) ->
        (
          exists v, get_R (getregs S) z = Some v /\
          (
            v = ($ 0) ->
            (
              exists fp fq L r,
                Spec (pc2, npc2) = Some (fp, fq) /\ S2 |= (fp L) ** r /\
                (fq L ** r) ==> q /\ DlyFrameFree r
            )
          ) /\
          ( 
            v <> ($ 0) ->
            safety_insSeq C S2 pc2 npc2 q Spec
          )
        )
    ) ->
    safety_insSeq C S pc npc q Spec

| ret_seq : forall C S pc npc q Spec,
    C pc = Some (cretl) ->
    (
      exists S1 S2 pc1 npc1 pc2 npc2,
        P__ C (S, pc, npc) (S1, pc1, npc1) /\
        P__ C (S1, pc1, npc1) (S2, pc2, npc2)
    ) ->
    (
      forall S1 S2 pc1 npc1 pc2 npc2,
        P__ C (S, pc, npc) (S1, pc1, npc1) ->
        P__ C (S1, pc1, npc1) (S2, pc2, npc2) ->
        (
          S2 |= q /\
          (exists f,
              get_R (getregs S2) r15 = Some f /\
              pc2 = f +ᵢ ($ 8) /\ npc2 = f +ᵢ ($ 12)
          )
        )
    ) ->
    safety_insSeq C S pc npc q Spec.

(*+ Safety +*)
Inductive safety : nat -> CodeHeap -> State -> Label -> Label -> asrt -> nat -> Prop :=
| safety_end :
    forall C S pc npc q k,
      safety 0 C S pc npc q k

| safety_cons : forall C S pc npc q n k,
    (
      forall i,
        C pc = Some (cntrans i) ->
        (
          (
            exists S' pc' npc',
              P__ C (S, pc, npc) (S', pc', npc')
          ) /\
          (
            forall S' pc' npc',
              P__ C (S, pc, npc) (S', pc', npc') ->
              safety n C S' pc' npc' q k
          )
        )
    ) ->
    (
      forall aexp rd,
        C pc = Some (cjumpl aexp rd) ->
        (
          (
            exists S1 S2 pc1 npc1 pc2 npc2,
              P__ C (S, pc, npc) (S1, pc1, npc1) /\ P__ C (S1, pc1, npc1) (S2, pc2, npc2)
          ) /\
          (
            forall S1 S2 pc1 npc1 pc2 npc2,
              P__ C (S, pc, npc) (S1, pc1, npc1) ->
              P__ C (S1, pc1, npc1) (S2, pc2, npc2) ->
              safety n C S2 pc2 npc2 q k
          )
        )
    ) ->
    (
      forall f,
        C pc = Some (cbe f) ->
        (
          (
            exists S1 S2 pc1 npc1 pc2 npc2,
              P__ C (S, pc, npc) (S1, pc1, npc1) /\ P__ C (S1, pc1, npc1) (S2, pc2, npc2)
          ) /\
          (
            forall S1 S2 pc1 npc1 pc2 npc2,
              P__ C (S, pc, npc) (S1, pc1, npc1) ->
              P__ C (S1, pc1, npc1) (S2, pc2, npc2) ->
              safety n C S2 pc2 npc2 q k
          )
        )
    ) ->
    (
      forall f,
        C pc = Some (cbne f) ->
        (
          (
            exists S1 S2 pc1 npc1 pc2 npc2,
              P__ C (S, pc, npc) (S1, pc1, npc1) /\ P__ C (S1, pc1, npc1) (S2, pc2, npc2)
          ) /\
          (
            forall S1 S2 pc1 npc1 pc2 npc2,
              P__ C (S, pc, npc) (S1, pc1, npc1) ->
              P__ C (S1, pc1, npc1) (S2, pc2, npc2) ->
              safety n C S2 pc2 npc2 q k
          )
        )
    ) ->
    (
      forall f,
        C pc = Some (ccall f) ->
        (
          (
            exists S1 S2 pc1 npc1 pc2 npc2,
              P__ C (S, pc, npc) (S1, pc1, npc1) /\ P__ C (S1, pc1, npc1) (S2, pc2, npc2)
          ) /\
          (
            forall S1 S2 pc1 npc1 pc2 npc2,
              P__ C (S, pc, npc) (S1, pc1, npc1) ->
              P__ C (S1, pc1, npc1) (S2, pc2, npc2) ->
              safety n C S2 pc2 npc2 q (Nat.succ k)
          )
        )
    ) ->
    (
      C pc = Some (cretl) ->
      (
        (
          exists S1 S2 pc1 npc1 pc2 npc2,
            P__ C (S, pc, npc) (S1, pc1, npc1) /\ P__ C (S1, pc1, npc1) (S2, pc2, npc2)
        ) /\
        (
          forall S1 S2 pc1 pc2 npc1 npc2,
            P__ C (S, pc, npc) (S1, pc1, npc1) ->
            P__ C (S1, pc1, npc1) (S2, pc2, npc2) ->
            (
              (Nat.eqb k 0 = true /\ S2 |= q) \/
              (Nat.eqb k 0 = false /\ safety n C S2 pc2 npc2 q (Nat.pred k))
            )
        )
      )
    ) ->
    safety (Nat.succ n) C S pc npc q k.

(*
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
*)

Definition cdhp_subst (Spec Spec' : funspec) :=
  forall f fsp, Spec f = Some fsp -> Spec' f = Some fsp.

(** Instruction Sequence rule Sound *)
Definition insSeq_sound (Spec : funspec) (p : asrt) (I : InsSeq) (q : asrt) :=
  forall C S pc npc,
    LookupC C pc npc I -> S |= p -> safety_insSeq C S pc npc q Spec.

(** Code Heap Sound *)
Definition cdhp_sound (Spec : funspec) (C : CodeHeap) (Spec' : funspec) :=
  forall f1 f2 fp fq L S,
    Spec' (f1, f2) = Some (fp, fq) -> S |= (fp L) ->
    cdhp_subst Spec Spec' ->
    exists I, LookupC C f1 f2 I /\ insSeq_sound Spec (fp L) I (fq L).