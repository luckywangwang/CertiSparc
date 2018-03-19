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

Require Import inssound.

Require Import Coq.Logic.FunctionalExtensionality.
 
Open Scope nat.
Open Scope code_scope.

Ltac get_ins_diff_false :=
  match goal with
  | H1 : ?C ?pc = _, H2 : ?C ?pc = _ |- _ =>
    rewrite H1 in H2; inversion H2;
    tryfalse; subst
  end.

Lemma insSeq_rule_sound :
  forall Spec Spec' p q I pc npc S C,
    wf_seq Spec p I q -> LookupC C pc npc I ->
    wf_cdhp Spec C Spec' -> cdhp_subst Spec Spec' -> S |= p ->
    safety C S pc npc q 0.
Proof.
  cofix.

  intros.
  eapply safety_cons.

  - (** Seq *)
    intros.
    inversion H0; subst; get_ins_diff_false.
    inversion H; subst.
    {
      (* Normal *)
      inversion H5; subst.
      inversion H18; get_ins_diff_false.
      clear H18.
      eapply ins_rule_sound in H14; eauto.
    }
    
  
Theorem cdhp_rule_sound :
  forall C Spec Spec',
    wf_cdhp Spec C Spec' ->
    cdhp_sound C Spec Spec'.
Proof.
  intros.
  unfolds cdhp_sound.
  intros.
  unfolds wf_cdhp.
  lets Hspec : H0. 
  eapply H with (L := L) in Hspec; eauto.
  simpljoin1. 
  rename x into I.
  eapply insSeq_rule_sound ; eauto.
Qed.

  