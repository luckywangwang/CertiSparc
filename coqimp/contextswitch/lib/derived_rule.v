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
   
Require Import lemmas.
Require Import lemmas_ins.

Require Import Coq.Logic.FunctionalExtensionality.

Require Import sep_lemma.
Require Import reg_lemma.

Open Scope nat.
Open Scope code_scope.
Open Scope mem_scope.
  
Print wf_seq.

Theorem forward_rule :
  forall p q q' Spec I,
    q ==> q' ->
    Spec |- {{ p }} I {{ q }} ->
    Spec |- {{ p }} I {{ q' }}.
Proof.
  intros.
  eapply Seq_conseq_rule; eauto.
Qed.

Theorem backward_rule :
  forall p p' q Spec I,
    p' ==> p ->
    Spec |- {{ p }} I {{ q }} ->
    Spec |- {{ p' }} I {{ q }}.
Proof.
  intros.
  eapply Seq_conseq_rule; eauto.
Qed.
  
Theorem ex_intro_rule' :
  forall I {tp : Type} (p q : tp -> asrt) (Spec : funspec),
    (forall x' : tp, Spec |- {{ p x' }} I {{ q x' }}) ->
    Spec |- {{ EX x : tp, p x }} I {{ EX x : tp, q x }}.
Proof.
  intros.
  eapply Ex_intro_rule; eauto.
  intros. 
  eapply forward_rule; [idtac | eauto].
  intros.
  simpl.
  eauto.
Qed.

Ltac hoare_ex_intro :=
  match goal with
  | |- _ |- {{ EX _, _ }} _ {{ EX _, _ }} =>
    eapply ex_intro_rule'; try intros;
    hoare_ex_intro
  | _ => idtac
  end.

Ltac hoare_lift_pre n :=
  let H' := fresh in
  match goal with
  | |- _ |- {{ _ }} _ {{ _ }} =>
    eapply backward_rule;
    [ introv H'; simpl_sep_liftn_in H' n; eapply H' | idtac]
  | _ => idtac
  end.