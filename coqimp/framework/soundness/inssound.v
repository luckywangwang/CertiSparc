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
Require Import soundness.

Open Scope nat.
Open Scope code_scope.

(*+ Soundness Proof of instruction +*)
Theorem ins_rule_sound : forall p q i,
    |- {{ p }} i {{ q }} ->
    ins_sound p q i.
Proof.
  intros.
  unfold ins_sound.
  destruct i; intros.
  - (* ld aexp rd *)
    rename a into aexp; rename g into rd.
    inversion H1; subst.
    inversion H; subst.
    