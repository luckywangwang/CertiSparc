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
  
Open Scope nat.
Open Scope code_scope.
Open Scope mem_scope.

Lemma astar_subst1 :
  forall p1 p1' p2 s,
    s |= p1 ** p2 -> p1 ==> p1' ->
    s |= p1' ** p2.
Proof.
  intros.
  sep_star_split_tac.
  simpl in H4.
  simpl.
  exists (m, (r, f), d) (m0, (r0, f0), d0).
  simpl.
  repeat (split; eauto).
Qed.

Lemma astar_subst2 :
  forall p1 p2 p2' s,
    s |= p1 ** p2 -> p2 ==> p2' ->
    s |= p1 ** p2'.
Proof.
  intros.
  sep_star_split_tac.
  simpl in H4.
  simpl.
  exists (m, (r, f), d) (m0, (r0, f0), d0).
  simpl.
  repeat (split; eauto).
Qed.

Theorem astar_assoc_intro :
  forall P Q R, P ** Q ** R ==> (P ** Q) ** R.
Proof.
  intros.
  eapply sep_star_assoc; eauto.
Qed.

Theorem astar_assoc_elim :
  forall P Q R, (P ** Q) ** R ==> P ** Q ** R.
Proof.
  intros.
  eapply sep_star_assoc2; eauto.
Qed.

Theorem astar_comm :
  forall P Q,
    P ** Q ==> Q ** P.
Proof.
  intros.
  eapply sep_star_sym; eauto.
Qed.

Lemma merge_empR_r_eq :
  forall R,
    merge R empR = R.
Proof.
  intros.
  unfold merge.
  eapply functional_extensionality; eauto.
  intro.
  destruct (R x); eauto.
Qed.

Lemma merge_empR_l_eq :
  forall R,
    merge empR R = R.
Proof.
  intros.
  unfold merge.
  eapply functional_extensionality; eauto.
Qed.

Lemma merge_empM_r_eq :
  forall M,
    merge M empM = M.
Proof.
  intros.
  unfold merge.
  eapply functional_extensionality; eauto.
  intro.
  destruct (M x); eauto.
Qed.

Lemma merge_empM_l_eq :
  forall M,
    merge empM M = M.
Proof.
  intros.
  unfold merge.
  eapply functional_extensionality; eauto.
Qed.
  
Lemma astar_emp_intro_r :
  forall p,
    p ==> p ** Aemp.
Proof.
  intros.
  destruct_state s.
  simpl.
  exists (m, (r, f), d) (empM, (empR, f), d).
  simpl.
  repeat (split; eauto).
  unfold disjoint.
  intro.
  destruct (m x); simpl; eauto.
  unfold disjoint.
  intro. 
  destruct (r x); simpl; eauto.
  rewrite merge_empR_r_eq; eauto.
  rewrite merge_empM_r_eq; eauto.
Qed.

Lemma astar_emp_elim_r :
  forall p,
    p ** Aemp ==> p.
Proof.
  intros.
  sep_star_split_tac.
  simpl in H3.
  simpljoin1.
  simpl in H2.
  simpljoin1.
  rewrite merge_empR_r_eq; eauto.
  rewrite merge_empM_r_eq; eauto.
Qed.
  
Lemma astar_emp_intro_l :
  forall p,
    p ==> Aemp ** p.
Proof.
  intros.
  destruct_state s.
  simpl.
  exists (empM, (empR, f), d) (m, (r, f), d).
  simpls.
  repeat (split; eauto).
  unfold disjoint.
  intro.
  simpl; eauto.
  destruct (m x); eauto.
  unfold disjoint.
  intro.
  simpl.
  destruct (r x); eauto.
Qed.

Lemma astar_emp_elim_l :
  forall p,
    Aemp ** p ==> p.
Proof.
  intros.
  sep_star_split_tac.
  simpls.
  simpljoin1.
  eauto.
Qed.
  
Ltac sassocr_in H :=
  match type of H with
    | _ |= (_ ** _) ** _ => apply astar_assoc_elim in H; sassocr_in H
    | _ => idtac
  end.

Ltac sassocl_in H :=
  match type of H with
    | _ |= _ ** (_ ** _) => apply astar_assoc_intro in H; sassocr_in H
    | _ => idtac
  end.

Ltac sassocr :=
  match goal with
    | |- _ |= (_ ** _) ** _ => apply astar_assoc_intro; sassocr
    | _ => idtac
  end.

Ltac sassocl :=
  match goal with
    | |- _ |= _ ** (_ ** _) => apply astar_assoc_elim; sassocl
    | _ => idtac
  end.

Ltac scomm_in H :=
  match type of H with
    | _ |= _ ** _ => apply astar_comm in H
    | _ => idtac
  end.

Ltac scomm :=
  match goal with
    | |- _ |= _ ** _ => apply astar_comm
    | _ => idtac
  end.

Tactic Notation "sep" "assocr" "in" hyp (H) :=
  sassocr_in H.
Tactic Notation "sep" "assocl" "in" hyp (H) :=
  sassocl_in H.
Tactic Notation "sep" "assocr" :=
  sassocr.
Tactic Notation "sep" "assocl" :=
  sassocl.
Tactic Notation "sep" "comm" "in" hyp (H) :=
  scomm_in H.
Tactic Notation "sep" "comm" :=
  scomm.

Ltac sliftn n :=
  match eval compute in n with
    | 0%nat => idtac
    | 1%nat => sep assocr
    | S ?n' => sep assocr; sep comm; sliftn n'
  end.

Ltac sliftn_in H n :=
  match eval compute in n with
    | 0%nat => idtac
    | 1%nat => sep assocr in H
    | S ?n' => sep assocr in H; sep comm in H; sliftn_in H n'
  end.

Fixpoint asrt_get_nth n p :=
  match n with
  | O => match p with
        | p1 ** p2 => p1
        | _ => p
        end
  | S n' =>
    match p with
    | p1 ** p2 => asrt_get_nth n' p2
    | _ => Aemp
    end
  end.

Fixpoint asrt_rm_nth n p :=
  match n with
  | O => match p with
        | p1 ** p2 => p2
        | _ => Aemp
        end
  | S n' =>
    match p with
    | p1 ** p2 => p1 ** asrt_rm_nth n' p2
    | _ => p
    end
  end.

Lemma asrt_lift_nth_stable :
  forall n p s,
    s |= p ->
    s |= asrt_get_nth n p ** asrt_rm_nth n p.
Proof.
  intro n.
  induction n; intros.
  -
    destruct p;
      simpl asrt_get_nth; simpl asrt_rm_nth;
        try solve [eapply astar_emp_intro_r; eauto].
    eauto.
  -
    destruct p;
      simpl asrt_get_nth; simpl asrt_rm_nth;
        try solve [eapply astar_emp_intro_l; eauto].
    specialize (IHn p2).
    eapply astar_subst2 in H; eauto.
    eapply sep_star_lift in H; eauto.
Qed.

Lemma asrt_lift_nth_stable_rev :
  forall n p s,
    s |= asrt_get_nth n p ** asrt_rm_nth n p ->
    s |= p.
Proof.
  intro n.
  induction n; intros.
  -
    destruct p;
      try solve
          [
            simpls asrt_get_nth; simpls asrt_rm_nth;
            eapply astar_emp_elim_r in H; eauto
          ].
    simpls; eauto.
  -
    destruct p;
      try solve
          [
            simpls asrt_get_nth; simpls asrt_rm_nth;
            eapply astar_emp_elim_l in H; eauto
          ].
    simpl asrt_get_nth in H.
    simpl asrt_rm_nth in H.
    specialize (IHn p2).
    eapply sep_star_lift in H.
    eapply astar_subst2 in H; eauto.
Qed.

Ltac simpl_sep_liftn_in H t :=
  match t with
  | 0%nat => idtac "n stars from 1, not 0"
  | S ?n' =>
    match type of H with
    | _ |= _ =>
        eapply asrt_lift_nth_stable with (n := n') in H;
        unfold asrt_get_nth in H; unfold asrt_rm_nth in H;
        try eapply astar_emp_elim_l in H;
        try eapply astar_emp_elim_r in H
    | _ => idtac "no assertion"
    end
  end.

Ltac simpl_sep_liftn t :=
  match t with
  | 0%nat => idtac "n stars from 1, not 0"
  | S ?n' =>
    match goal with
    | |- _ |= _ =>
      eapply asrt_lift_nth_stable_rev with (n := n');
      unfold asrt_get_nth; unfold asrt_rm_nth;
      try eapply astar_emp_intro_r;
      try eapply astar_emp_intro_l
    | _ => idtac "no assertion"
    end
  end.

Fixpoint asrt_combine_to_line (p1 : asrt) (p2 : asrt) (n : nat) :=
  match n with
  | 0%nat => p1 ** p2
  | S n' =>
    match p1 with
    | p1' ** p2' => p1' ** (asrt_combine_to_line p2' p2 n')
    | _ => p1 ** p2
    end
  end.

Lemma asrt_combine_to_line_stable :
  forall n p1 p2 s,
    s |= p1 ** p2 ->
    s |= asrt_combine_to_line p1 p2 n.
Proof.
  intro n.
  induction n; intros.
  -
    destruct p1; simpls; eauto.
  -
    destruct p1;
      try solve [simpls; eauto].
    simpl.
    sep_star_split_tac.
    simpl in H1, H3.
    simpljoin1.
    exists (m1, (r1, f2), d2) (merge m2 m0, (merge r2 r0, f2), d2).
    simpl; repeat (split; eauto).
    eapply disj_sep_merge_still; eauto.
    eapply disj_sym in H3.
    eapply disj_merge_disj_sep1 in H3; eauto.
    eapply disj_sym; eauto.
    eapply disj_sep_merge_still; eauto.
    eapply disj_sym in H4; eauto.
    eapply disj_merge_disj_sep1 in H4; eauto.
    eapply disj_sym; eauto.
    do 2 rewrite merge_assoc; eauto.
    eapply IHn; eauto.
    simpl.
    do 2 eexists.
    simpl; repeat (split; eauto).
    eapply disj_sym in H3.
    eapply disj_merge_disj_sep2 in H3; eauto.
    eapply disj_sym; eauto.
    eapply disj_sym in H4.
    eapply disj_merge_disj_sep2 in H4; eauto.
    eapply disj_sym; eauto.
Qed.