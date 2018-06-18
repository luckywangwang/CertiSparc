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

Theorem forward_rule :
  forall p q q' Spec I f,
    q ==> q' ->
    Spec |- {{ p }} f # I {{ q }} ->
    Spec |- {{ p }} f # I {{ q' }}.
Proof.
  intros.
  eapply Seq_conseq_rule; eauto.
Qed.

Theorem backward_rule :
  forall p p' q Spec I f,
    p' ==> p ->
    Spec |- {{ p }} f # I {{ q }} ->
    Spec |- {{ p' }} f # I {{ q }}.
Proof.
  intros.
  eapply Seq_conseq_rule; eauto.
Qed.
  
Theorem ex_intro_rule' :
  forall I {tp : Type} (p q : tp -> asrt) (Spec : funspec) f,
    (forall x' : tp, Spec |- {{ p x' }} f # I {{ q x' }}) ->
    Spec |- {{ EX x : tp, p x }} f # I {{ EX x : tp, q x }}.
Proof.
  intros.
  eapply Ex_intro_rule; eauto.
  intros. 
  eapply forward_rule; [idtac | eauto].
  intros.
  simpl.
  eauto.
Qed.

Theorem disj_sep_rule :
  forall p1 p2 p q I Spec f,
    Spec |- {{ p1 ** p }} f # I {{ q }} ->
           Spec |- {{ p2 ** p }} f # I {{ q }} ->
                  Spec |- {{ (p1 \\// p2) ** p }} f # I {{ q }}.
Proof.
  intros.
  assert (Ht : Spec |- {{(p1 ** p) \\// (p2 ** p)}} f # I {{q \\// q}}).
  {
    eapply Seq_disj_rule; eauto.
  }
  eapply Seq_conseq_rule.
  eapply Ht.
  clear.
  introv Hs.
  sep_star_split_tac.
  simpl in H3.
  simpljoin1.
  simpl in H1.
  simpl.
  destruct H1.
  left.
  do 2 eexists.
  simpl; repeat (split; eauto).
  right.
  do 2 eexists.
  simpl; repeat (split; eauto).
  introv Hs.
  simpl in Hs; destruct Hs; eauto.
Qed.

Theorem Afalse_sep_rule :
  forall p q I Spec f,
    Spec |- {{ Afalse ** p }} f # I {{ q }}.
Proof.
  intros.
  eapply Seq_conseq_rule.
  eapply Seq_false_rule; eauto.
  2 : eauto.
  introv Hs.
  sep_star_split_tac.
  simpls.
  tryfalse.
Qed.

Ltac hoare_lift_pre n :=
  let H' := fresh in
  match goal with
  | |- _ |- {{ _ }} _ # _ {{ _ }} =>
    eapply backward_rule;
    [ introv H'; simpl_sep_liftn_in H' n; eapply H' | idtac]
  | _ => idtac
  end.

Theorem aexists_intro :
  forall {t : Type} (P : t->asrt) s,
  (exists x, s |= P x) -> s |= EX x, P x.
Proof.
  intros.
  simpljoin1.
  simpl; eauto.
Qed.

Theorem aexists_elim :
  forall {t : Type} (P : t->asrt) s,
    s |= EX x, P x -> (exists x, s |= P x).
Proof.
  intros.
  simpls; eauto.
Qed.

Theorem astar_r_aexists_intro :
  forall {t:Type} P (Q:t->asrt),
    EX x, (P ** Q x) ==> P ** EX x, Q x.
Proof.
  intros.
  simpls.
  simpljoin1.
  destruct_state x0.
  destruct_state x1.
  simpls.
  simpljoin1.
  exists (m, (r, f0), d0) (m0, (r0, f0), d0).
  simpl; repeat (split; eauto).
Qed.

Theorem astar_l_aexists_intro :
  forall {t:Type} (P:t->asrt) Q,
    EX x, (P x ** Q) ==> (EX x, P x) ** Q.
Proof.
  intros.
  simpls.
  simpljoin1.
  destruct_state x0.
  destruct_state x1.
  simpls.
  simpljoin1.
  exists (m, (r, f0), d0) (m0, (r0, f0), d0).
  simpl; repeat (split; eauto).
Qed.

Theorem astar_r_aexists_elim :
  forall {t:Type} P (Q:t->asrt),
    P ** (EX x, Q x) ==> EX x, (P ** Q x).
Proof.
  intros.
  simpl in *.
  simpljoin1.
  destruct_state x.
  destruct_state x0.
  simpls.
  simpljoin1.
  exists x1 (m, (r, f0), d0) (m0, (r0, f0), d0).
  simpl; repeat (split; eauto).
Qed.

Theorem astar_l_aexists_elim :
  forall {t:Type} (P:t->asrt) Q,
    (EX x, P x) ** Q ==> EX x, (P x ** Q).
Proof.
  intros.
  simpl in *.
  simpljoin1.
  destruct_state x.
  destruct_state x0.
  simpls.
  simpljoin1.
  exists x1 (m, (r, f0), d0) (m0, (r0, f0), d0).
  simpl; repeat (split; eauto).
Qed.

Theorem aconj_r_aexists_intro :
  forall {t:Type} P (Q:t->asrt),
    EX x, (P //\\ Q x) ==> P //\\ EX x, Q x.
Proof.
  intros.
  simpl in *.
  simpljoin1.
  split; eauto.
Qed.

Theorem aconj_l_aexists_intro :
  forall {t:Type} (P:t->asrt) Q,
    EX x, (P x //\\ Q) ==> (EX x, P x) //\\ Q.
Proof.
  intros.
  simpl in *.
  simpljoin1.
  split; eauto.
Qed.

Theorem aconj_r_aexists_elim :
  forall {t:Type} P (Q:t->asrt),
    P //\\ (EX x, Q x) ==> EX x, (P //\\ Q x).
Proof.
  intros.
  simpl in *.
  simpljoin1; eauto.
Qed.

Theorem aconj_l_aexists_elim :
  forall {t:Type} (P:t->asrt) Q,
    (EX x, P x) //\\ Q ==> EX x, (P x //\\ Q).
Proof.
  intros.
  simpl in *.
  simpljoin1; eauto.
Qed.

Theorem adisj_r_aexists_intro :
  forall {t:Type} P (Q:t->asrt),
    EX x, (P \\// Q x) ==> P \\// EX x, Q x.
Proof.
  intros.
  simpl in *.
  simpljoin1.
  destruct H; eauto.
Qed.

Theorem adisj_l_aexists_intro :
  forall {t:Type} (P:t->asrt) Q,
    EX x, (P x \\// Q) ==> (EX x, P x) \\// Q.
Proof.
  intros.
  simpl in *.
  simpljoin1.
  destruct H; eauto.
Qed.

Theorem adisj_r_aexists_elim :
  forall {t:Type} P (Q:t->asrt),
    (exists (x:t), x = x) ->
    P \\// (EX x, Q x) ==> EX x, (P \\// Q x).
Proof.
  intros.
  simpls. 
  simpljoin1.
  destruct H0; eauto.
  simpljoin1.
  eauto.
  Unshelve.
  exact x.
Qed.

Theorem adisj_l_aexists_elim :
  forall {t:Type} (P:t->asrt) Q,
    (exists (x:t), x = x) ->
    (EX x, P x) \\// Q ==> EX x, (P x \\// Q).
Proof.
  intros.
  simpls.
  simpljoin1.
  destruct H0; eauto.
  simpljoin1; eauto.
  Unshelve.
  exact x.
Qed.

Ltac sep_ex_intro :=
  match goal with
  | |- ?s |= (EX _, _) =>
    eapply aexists_intro; eexists; sep_ex_intro
  | |- ?s |= (EX _, _) ** ?p =>
    eapply astar_l_aexists_intro; sep_ex_intro
  | |- ?s |= ?p ** (EX _, _) =>
    eapply astar_r_aexists_intro; sep_ex_intro
  | |- ?s |= (EX _, _) //\\ ?p =>
    eapply aconj_l_aexists_intro; sep_ex_intro
  | |- ?s |= ?p //\\ (EX _, _) =>
    eapply aconj_r_aexists_intro; sep_ex_intro
  | |- ?s |= (EX _, _) \\// ?p =>
    eapply adisj_l_aexists_intro; sep_ex_intro
  | |- ?s |= ?p \\// (EX _, _) =>
    eapply adisj_r_aexists_intro; sep_ex_intro
  | _ => idtac
  end.

Theorem sep_pure_l_intro :
  forall (pu : Prop) p s,
    pu -> s |= p -> s |= [| pu |] ** p.
Proof.
  intros.
  simpl.
  destruct_state s.
  exists (empM, (empR, f), d) (m, (r, f), d).
  simpl; repeat (split; eauto).
  unfold disjoint.
  intros; eauto.
  simpl.
  destruct (m x); eauto.
  unfold disjoint.
  intros; eauto.
  simpl.
  destruct (r x); eauto.
Qed.

Theorem sep_pure_r_intro :
  forall (pu : Prop) p s,
    pu -> s |= p -> s |= p ** [| pu |].
Proof.
  intros.
  destruct_state s.
  simpl.
  exists (m, (r, f), d) (empM, (empR, f), d).
  simpl; repeat (split; eauto).
  unfold disjoint.
  intros.
  destruct (m x); simpl; eauto.
  unfold disjoint.
  intros.
  destruct (r x); simpl; eauto.
  rewrite merge_empR_r_eq; eauto.
  rewrite merge_empM_r_eq; eauto.
Qed.

Theorem sep_pure_l_elim :
  forall (pu : Prop) p s,
    s |= [| pu |] ** p -> pu /\ s |= p.
Proof.
  intros.
  sep_star_split_tac.
  simpls.
  simpljoin1.
  split; eauto.
Qed.

Theorem sep_pure_r_elim :
  forall (pu : Prop) p s,
    s |= p ** [| pu |] -> pu /\ s |= p.
Proof.
  intros.
  sep_star_split_tac.
  simpls.
  simpljoin1.
  split; eauto.
  rewrite empM_merge_still_r; eauto.
  rewrite merge_empR_r_eq; eauto.
Qed.

Ltac sep_ex_elim_in H :=
  match type of H with
  | ?s |= (EX _, _) =>
    eapply aexists_elim in H; destruct H as [?x H]; sep_ex_elim_in H
  | ?s |= (EX _, _) ** ?p =>
    eapply astar_l_aexists_elim in H; destruct H as [?x H]; sep_ex_elim_in H
  | ?s |= ?p ** (EX _, _) =>
    eapply astar_r_aexists_elim in H; destruct H as [?x H]; sep_ex_elim_in H
  | ?s |= (EX _, _) //\\ ?p =>
    eapply aconj_l_aexists_elim in H; destruct H as [?x H]; sep_ex_elim_in H
  | ?s |= ?p //\\ (EX _, _) =>
    eapply aconj_r_aexists_elim in H; destruct H as [?x H]; sep_ex_elim_in H
  | ?s |= (EX _, _) \\// ?p =>
    eapply adisj_l_aexists_elim in H; destruct H as [?x H]; sep_ex_elim_in H
  | ?s |= ?p \\// (EX _, _) =>
    eapply adisj_r_aexists_elim in H; destruct H as [?x H]; sep_ex_elim_in H
  | _ => idtac
  end.

Theorem sep_disj_l_intro :
  forall p1 p2 p s,
    s |= p1 ** p \/ s |= p2 ** p ->
    s |= (p1 \\// p2) ** p.
Proof.
  intros.
  simpls.
  destruct H; simpljoin1; eauto.
  exists x x0.
  repeat (split; eauto).
  exists x x0.
  repeat (split; eauto).
Qed.

Theorem sep_disj_r_intro :
  forall p1 p2 p s,
    s |= p ** p1 \/ s |= p ** p2 ->
    s |= p ** (p1 \\// p2).
Proof.
  intros.
  simpls.
  destruct H; simpljoin1; eauto.
  exists x x0.
  repeat (split; eauto).
  exists x x0.
  repeat (split; eauto).
Qed.

Lemma hoare_pure_gen' : forall P Q (pu:Prop) Spec I f,
    (forall S, S |= P -> pu) ->
    Spec |- {{ [| pu |] ** P }} f # I {{ Q }} ->
    Spec |- {{ P }} f # I {{ Q }}.
Proof.
  intros.
  eapply backward_rule with (p := ([| pu |] ** P)); eauto.
  intros.
  lets Ht : H1.
  eapply H in Ht.
  eapply sep_pure_l_intro; eauto.
Qed.

Theorem ex_intro_l_rule :
  forall {tp : Type} (p : tp -> asrt) p' q I Spec f,
    (forall x' : tp, Spec |- {{ p x' ** p' }} f # I {{ q }}) ->
    Spec |- {{ (EX x : tp, p x) ** p' }} f # I {{ q }}.
Proof.
  intros.
  eapply backward_rule.
  introv Hs.
  eapply astar_l_aexists_elim in Hs; eauto.
  eapply Ex_intro_rule; eauto.
Qed.
  
Ltac hoare_ex_intro :=
  match goal with
  | |- _ |- {{ EX _, _ }} _ # _ {{ EX _, _ }} =>
    eapply ex_intro_rule'; try intros;
    hoare_ex_intro
  | _ => idtac
  end.

Ltac hoare_ex_intro_pre :=
  match goal with
  | |- _ |- {{ EX _, _ }} _ # _ {{ _ }} =>
    eapply Ex_intro_rule; try intros;
    hoare_ex_intro_pre
  | |- _ |- {{ (EX _, _) ** _ }} _ # _ {{ _ }} =>
    eapply ex_intro_l_rule; try intros;
    hoare_ex_intro_pre
  | _ => idtac
  end.