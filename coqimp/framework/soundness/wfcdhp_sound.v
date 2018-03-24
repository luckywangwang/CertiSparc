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
Open Scope mem_scope.

Ltac get_ins_diff_false :=
  match goal with
  | H1 : ?C ?pc = _, H2 : ?C ?pc = _ |- _ =>
    rewrite H1 in H2; inversion H2;
    tryfalse; subst
  end.

Ltac elim_ins_neq :=
  match goal with
  | H : LookupC _ _ _ _ |- _ =>
    inversion H; subst; get_ins_diff_false
  | _ => idtac
  end.

(*+ Lemmas for Memory +*)
Lemma disj_sep_merge_still :
  forall tp (m m1 m2 : tp -> option Word),
    disjoint m m1 -> disjoint m m2 ->
    disjoint m (merge m1 m2).
Proof.
  intros.
  unfold disjoint in *.
  intros.
  specialize (H x).
  specialize (H0 x).
  destruct (m x) eqn:Heqe; eauto.
  {
    unfold merge.
    destruct (m1 x) eqn:Heqe1; eauto.
  }
  {
    unfold merge.
    destruct (m1 x) eqn:Heqe1; eauto.
  }
Qed.

Lemma disj_merge_disj_sep1 :
  forall tp (m1 m2 m3 : tp -> option Word),
    disjoint m1 (merge m2 m3) ->
    disjoint m1 m2.
Proof.
  intros.
  unfold disjoint in *.
  intros.
  specialize (H x).
  destruct (m1 x); eauto.
  unfold merge in *.
  destruct (m2 x); eauto.
  unfold merge in *.
  destruct (m2 x); eauto.
Qed.

Lemma disj_merge_disj_sep2 :
  forall tp (m1 m2 m3 : tp -> option Word),
    disjoint m1 (merge m2 m3) ->
    disjoint m1 m3.
Proof.
  intros.
  unfold disjoint in *.
  intros.
  specialize (H x).
  destruct (m1 x).
  unfold merge in *.
  destruct (m2 x) eqn:Heqe1; tryfalse; eauto.
  unfold merge in *.
  destruct (m2 x) eqn:Heqe1; tryfalse; eauto.
  destruct (m3 x); eauto.
Qed.

Lemma merge_assoc :
  forall tp (m1 m2 m3 : tp -> option Word),
    merge m1 (merge m2 m3) = merge (merge m1 m2) m3.
Proof.
  intros.
  unfold merge.
  eapply functional_extensionality.
  intros.
  destruct (m1 x) eqn:Heqe1;
    destruct (m2 x) eqn:Heqe2;
    simpl; tryfalse; eauto.
Qed.

Lemma merge_lift :
  forall tp (m1 m2 m3 : tp -> option Word),
    disjoint m1 m2 ->
    merge m1 (merge m2 m3) = merge m2 (merge m1 m3).
Proof.
  intros.
  unfold merge.
  eapply functional_extensionality; eauto.
  intros.
  destruct (m1 x) eqn:Heqe1;
    destruct (m2 x) eqn:Heqe2; tryfalse; eauto.
  unfold disjoint in *.
  specialize (H x).
  rewrite Heqe1 in H;
    rewrite Heqe2 in H; tryfalse.
Qed.

Lemma get_vl_merge_still :
  forall tp (M m : tp -> option Word) l v,
    M l = Some v ->
    merge M m l = Some v.
Proof.
  intros.
  unfold merge in *.
  rewrite H; eauto.
Qed.

Lemma get_vl_merge_still2 :
  forall tp (M m : tp -> option Word) l v,
    disjoint M m -> m l = Some v ->
    merge M m l = Some v.
Proof.
  intros.
  unfold merge in *.
  destruct (M l) eqn:Heqe; tryfalse.
  unfold disjoint in *.
  specialize (H l).
  rewrite Heqe in H.
  rewrite H0 in H.
  tryfalse.
  eauto.
Qed.

(*+ Lemmas for exe_delay +*)
Lemma exe_delay_no_abort :
  forall D R,
  exists R' D', exe_delay R D = (R', D').
Proof.
  intro D.
  induction D; intros.
  simpl.
  eauto.
  destruct a, p.
  simpl.
  destruct d.
  {
    specialize (IHD R).
    simpljoin1.
    rewrite H.
    eauto.
  }
  {
    specialize (IHD R).
    simpljoin1.
    rewrite H.
    eauto.
  }
Qed.

Lemma asrt_dlyfrm_free_elim_head_stable :
  forall p M R F D d,
    (M, (R, F), d :: D) |= p -> DlyFrameFree p ->
    (M, (R, F), D) |= p.
Proof.
  intro p.
  induction p; intros;
    try solve [unfolds DlyFrameFree; simpls; tryfalse];
    try solve [simpls; eauto].
  -
    simpls.
    unfolds regSt.
    simpls.
    simpljoin1.
    repeat (split; eauto).
    intro.
    eapply H2.
    clear H2.
    unfolds regInDlyBuff.
    destruct r; tryfalse.
    destruct d, p.
    simpls; eauto.
  -
    simpls.
    simpljoin1; eauto.
  -
    simpls.
    simpljoin1.
    destruct H; eauto.
  -
    sep_star_split_tac.
    simpl in H4.
    simpljoin1.
    simpl in H0.
    simpljoin1.
    eapply IHp1 in H; eauto.
    eapply IHp2 in H3; eauto.
    simpl.
    exists (m, (r, f0), D) (m0, (r0, f0), D).
    simpl; repeat (split; eauto).
  -
    simpls.
    simpljoin1.
    specialize (H1 x).
    exists x.
    eauto.
Qed.

Lemma dly_frm_free_exe_delay_stable :
  forall p D M R R' D' F,
    (M, (R, F), D) |= p -> DlyFrameFree p ->
    exe_delay R D = (R', D') ->
    (M, (R', F), D') |= p.
Proof.
  intro p.
  induction p; intros;
    try solve [simpls; eauto; tryfalse].
  eapply dly_reduce_Aemp_stable; eauto.
  eapply dly_reduce_Amapsto_stable; eauto.
  eapply dly_reduce_Aaexp_stable; eauto.
  eapply dly_reduce_Aoexp_stable; eauto.
  eapply dly_reduce_reg_stable; eauto.
  simpls.
  simpljoin1.
  eauto.
  simpls.
  simpljoin1.
  destruct H; eauto.
  sep_star_split_tac.
  simpl in H5.
  simpljoin1.
  simpl in H0.
  simpljoin1.
  eapply exe_dly_sep_split in H1; eauto.
  simpljoin1.
  eapply IHp1 in H; eauto.
  eapply IHp2 in H4; eauto.
  simpljoin1.
  simpl.
  do 2 eexists; eauto.
  repeat (split; eauto).
  simpls.
  simpljoin1.
  exists x.
  eauto.
Qed.

Lemma exe_delay_general_reg_stable :
  forall D R R' D' (r : GenReg),
    exe_delay R D = (R', D') ->
    (forall v, R r = Some v <-> R' r = Some v).
Proof.
  intro D.
  induction D; intros.
  -
    simpls.
    inversion H; subst.
    split; eauto.

  -
    destruct a, p.
    simpl in H.
    destruct d.
    {
      destruct (exe_delay R D) eqn:Heqe.
      inversion H; subst.
      eapply IHD in Heqe; eauto.
      split.
      intro.
      eapply Heqe in H0.
      unfold set_R.
      unfold is_indom.
      destruct (r0 s) eqn:Heqe1; eauto.
      unfold RegMap.set.
      destruct_rneq.
      intro.
      eapply Heqe; eauto.
      clear - H0.
      unfolds set_R.
      unfold is_indom in *.
      destruct (r0 s) eqn:Heqe; tryfalse; tryfalse; eauto.
      unfolds RegMap.set.
      destruct_rneq_H.
    }
    {
      destruct (exe_delay R D) eqn:Heqe.
      inversion H; subst.
      eapply IHD in Heqe; eauto.
    }
Qed.
    
(*+ Lemmas for expression +*)
Lemma eval_addrexp_merge_still :
  forall M m aexp l,
    eval_addrexp M aexp = Some l ->
    eval_addrexp (merge M m) aexp = Some l.
Proof.
  intros.
  destruct aexp.
  -
    simpl in H.
    simpl.
    destruct o.
    +
      simpls.
      unfold merge.
      rewrite H; eauto.
    +
      simpls.
      destruct (($ (-4096)) <=ᵢ w && w <=ᵢ ($ 4095)); eauto.
  -
    simpls.
    destruct (M g) eqn:Heqe.
    +
      unfold merge in *.
      rewrite Heqe; eauto.
      destruct o.
      simpls.
      destruct (M g0) eqn:Heqe1.
      eauto.
      tryfalse.
      unfolds eval_opexp.
      destruct (($ (-4096)) <=ᵢ w0 && w0 <=ᵢ ($ 4095)); eauto.
    +
      tryfalse.
Qed.

Lemma eval_opexp_merge_still :
  forall M m oexp l,
    eval_opexp M oexp = Some l ->
    eval_opexp (merge M m) oexp = Some l.
Proof.
  intros.
  destruct oexp.
  -
    simpls.
    unfold merge in *.
    rewrite H; eauto.
  -
    simpls.
    destruct (($ (-4096)) <=ᵢ w && w <=ᵢ ($ 4095)); eauto.
Qed.
  
  
(*+ Lemmas for instruction +*)

Lemma exe_delay_safety_property :
  forall D (R R' R1 : RegFile) M D' F r,
    (R', D') = exe_delay R D -> disjoint R R1 ->
    (M, (R1, F), D) |= r -> DlyFrameFree r ->
    exists R1', disjoint R' R1' /\ (merge R' R1', D') = exe_delay (merge R R1) D /\
           (R1', D') = exe_delay R1 D /\ (M, (R1', F), D') |= r.
Proof.
  intro D.
  induction D; intros.
  - 
    simpl in H.
    inversion H; subst.
    exists R1.
    repeat (split; eauto).
  -
    destruct a, p.
    simpl in H.
    destruct d.
    { 
      destruct (exe_delay R D) eqn:Heqe.
      inversion H; subst.
      lets Hr : H1.
      lets Hdly : Heqe.
      eapply asrt_dlyfrm_free_elim_head_stable in H1; eauto.
      symmetry in Heqe.
      eapply IHD in Heqe; eauto.
      simpljoin1.
      rename x into R1'.
      destruct (indom_nor_not s r0).
      { 
        exists R1'.
        repeat (split; eauto).
        eapply disjoint_setR_still1; eauto.
        simpl.
        rewrite <- H4. 
        rewrite indom_setR_merge_eq1; eauto.
        simpl.
        rewrite <- H5; eauto.
        rewrite not_indom_set_R_stable; eauto.
        eapply indom_m1_disj_notin_m2 in H3; eauto.
      }
      { 
        exists (set_R R1' s w).
        repeat (split; eauto).
        eapply disjoint_setR_still1; eauto.
        eapply disjoint_setR_still2; eauto.
        simpl.
        rewrite <- H4.
        rewrite not_indom_set_R_stable; eauto.
        rewrite indom_setR_merge_eq2; eauto.
        simpl.
        rewrite <- H5.
        eauto.
        assert ((set_R R1' s w, d) = exe_delay R1 ((0, s, w) :: D)).
        {
          simpl.
          rewrite <- H5; eauto.
        }
        clear H4 H5 H6.
        eapply dly_frm_free_exe_delay_stable; eauto.
      }
    }
    {
      destruct (exe_delay R D) eqn:Heqe.
      inversion H; subst.
      symmetry in Heqe.
      lets Ht : H1.
      eapply asrt_dlyfrm_free_elim_head_stable in Ht; eauto.
      eapply IHD in Ht; eauto.
      simpljoin1.
      exists x.
      repeat (split; eauto).
      simpl.
      rewrite <- H4; eauto.
      simpl.
      rewrite <- H5; eauto.
      assert ((x, (d, s, w) :: d0) = exe_delay R1 ((S d, s, w) :: D)).
      {
        simpl.
        rewrite <- H5; eauto.
      }

      clear H4 H5 H6.
      eapply dly_frm_free_exe_delay_stable; eauto.
    }
Qed.
    
Lemma program_step_safety_property :
  forall s1 s1' s2 s r pc pc' npc npc' C,
    state_union s1 s2 s -> (P__ C (s1, pc, npc) (s1', pc', npc')) ->
    s2 |= r -> DlyFrameFree r ->
    exists s' s2',
      P__ C (s, pc, npc) (s', pc', npc') /\ state_union s1' s2' s' /\
      s2' |= r.
Proof.
  intros.
  destruct_state s1.
  destruct_state s2.
  destruct_state s.
  simpl in H.
  simpljoin1.
  inversion H0; subst.
  eapply exe_delay_safety_property in H7; eauto.
  simpljoin1.
  rename x into R1'.
  inversion H15; subst.
  - (** NTrans ins *)
    eapply ins_safety_property in H17; eauto.
    simpljoin1.
    destruct_state x.
    destruct_state x0.
    do 2 eexists.
    split.
    econstructor.
    eapply H5.
    eapply NTrans; eauto.
    split; eauto.
    simpl.
    repeat (split; eauto).
  - (** jumpl *)
    do 2 eexists.
    split.
    econstructor; eauto.
    eapply Jumpl; eauto.
    eapply eval_addrexp_merge_still; eauto.
    eapply indom_merge_still; eauto.
    split; eauto.
    simpl.
    repeat (split; eauto).
    eapply disjoint_setR_still1; eauto.
    rewrite indom_setR_merge_eq1; eauto.
  - (** call *)
    do 2 eexists.
    split.
    econstructor; eauto.
    eapply Call; eauto.
    eapply indom_merge_still; eauto.
    split; eauto.
    simpl.
    repeat (split; eauto).
    eapply disjoint_setR_still1; eauto.
    rewrite indom_setR_merge_eq1; eauto.
  - (** retl *)
    do 2 eexists.
    split.
    econstructor; eauto.
    eapply Retl; eauto.
    clear - H23.
    unfold merge.
    rewrite H23; eauto.
    split; eauto.
    simpl.
    repeat (split; eauto).
  - (** be-true *)
    do 2 eexists.
    split.
    econstructor; eauto.
    eapply Be_true; eauto.
    eapply eval_addrexp_merge_still; eauto.
    unfold merge.
    rewrite H24; eauto.
    split; eauto.
    simpls.
    repeat (split; eauto).
  - (** be-false *)
    do 2 eexists.
    split.
    econstructor; eauto.
    eapply Be_false; eauto.
    eapply eval_addrexp_merge_still; eauto.
    unfold merge.
    rewrite H24; eauto.
    split; eauto.
    simpls.
    repeat (split; eauto).
  - (** bne-true *)
    do 2 eexists.
    split.
    econstructor; eauto.
    eapply Bne_true; eauto.
    eapply eval_addrexp_merge_still; eauto.
    unfold merge.
    rewrite H24; eauto.
    split; eauto.
    simpls.
    repeat (split; eauto).
  - (** bne-false *)
    do 2 eexists.
    split.
    econstructor; eauto.
    eapply Bne_false; eauto.
    eapply eval_addrexp_merge_still; eauto.
    unfold merge.
    rewrite H24; eauto.
    split; eauto.
    simpls.
    repeat (split; eauto).
Qed.

Lemma program_step_deterministic :
  forall s s1 s2 C pc npc pc1 npc1 pc2 npc2,
    P__ C (s, pc, npc) (s1, pc1, npc1) -> P__ C (s, pc, npc) (s2, pc2, npc2) ->
    s1 = s2 /\ pc1 = pc2 /\ npc1 = npc2.
Proof.
  intros.
  inversion H; subst.
  inversion H0; subst.
  rewrite <- H4 in H5.
  inversion H5; subst.
  inversion H9; subst;
    inversion H14; get_ins_diff_false; eauto.
  -
    eapply ins_exec_deterministic in H12; eauto.
  -
    rewrite H19 in H23.
    inversion H23; eauto.
  -
    rewrite H19 in H21.
    inversion H21; subst; eauto.
  -
    rewrite H19 in H24.
    inversion H24; tryfalse.
    eauto.
  -
    rewrite H19 in H23.
    inversion H23; subst; eauto.
Qed.

(*+ Lemmas for Sep Star +*)
Lemma disj_sep_star_merge :
  forall m1 m2 R1 R2 F D p1 p2,
    (m1, (R1, F), D) |= p1 ->
    (m2, (R2, F), D) |= p2 ->
    disjoint m1 m2 -> disjoint R1 R2 ->
    (merge m1 m2, (merge R1 R2, F), D) |= p1 ** p2.
Proof.
  intros.
  simpl.
  exists (m1, (R1, F), D) (m2, (R2, F), D).
  repeat (split; eauto).
Qed.

Lemma sep_star_assoc :
  forall s p1 p2 p3,
    s |= p1 ** p2 ** p3 ->
    s |= (p1 ** p2) ** p3.
Proof.
  intros.
  destruct_state s.
  sep_star_split_tac.
  simpl in H2, H3.
  simpljoin1.
  simpl. 
  exists (merge m0 m2, (merge r0 r2, f3), d3) (m3, (r3, f3), d3).
  repeat (split; eauto). 
  eapply disj_sym. 
  eapply disj_sep_merge_still; eauto.
  eapply disj_merge_disj_sep2 in H3.
  eapply disj_sym; eauto. 
  eapply disj_sym; eauto.
  eapply disj_sym. 
  eapply disj_sep_merge_still; eauto.
  eapply disj_merge_disj_sep2 in H4.
  eapply disj_sym; eauto. 
  eapply disj_sym; eauto.
  do 2 rewrite merge_assoc; eauto.
 
  exists (m0, (r0, f3), d3) (m2, (r2, f3), d3).
  repeat (split; eauto).
  eapply disj_merge_disj_sep1 in H3; eauto.
  eapply disj_merge_disj_sep1 in H4; eauto.
Qed.

Lemma sep_star_assoc2 :
  forall s p1 p2 p3,
    s |= (p1 ** p2) ** p3 ->
    s |= p1 ** p2 ** p3.
Proof.
  intros.
  destruct_state s.
  sep_star_split_tac.
  simpls.
  simpljoin1. 
  exists (m2, (r2, f3), d3) (merge m3 m1, (merge r3 r1, f3), d3).
  repeat (split; eauto).
  eapply disj_sep_merge_still; eauto.
  eapply disj_sym in H3.
  eapply disj_merge_disj_sep1 in H3; eauto.
  eapply disj_sym; eauto.

  eapply disj_sep_merge_still; eauto.
  eapply disj_sym in H4.
  eapply disj_merge_disj_sep1 in H4; eauto.
  eapply disj_sym; eauto.

  do 2 rewrite merge_assoc; eauto.
  exists (m3, (r3, f3), d3) (m1, (r1, f3), d3).
  repeat (split; eauto).
  eapply disj_sym in H3.
  eapply disj_merge_disj_sep2 in H3.
  eapply disj_sym; eauto.
  eapply disj_sym in H4.
  eapply disj_merge_disj_sep2 in H4.
  eapply disj_sym; eauto.
Qed.

Lemma sep_star_sym :
  forall s p1 p2,
    s |= p1 ** p2 ->
    s |= p2 ** p1.
Proof.
  intros.
  simpls.
  simpljoin1.
  exists x0 x.
  repeat (split; eauto).
  destruct_state x.
  destruct_state x0.
  simpls.
  simpljoin1. 
  repeat (split; eauto).
  eapply disj_sym; eauto.
  eapply disj_sym; eauto.
  rewrite disj_merge_reverse_eq; eauto.
  assert (r ⊎ r0 = r0 ⊎ r).
  {
    rewrite disj_merge_reverse_eq; eauto.
  }
  rewrite H3; eauto.
Qed.

Lemma sep_star_lift :
  forall s p1 p2 p3,
    s |= p1 ** p2 ** p3 ->
    s |= p2 ** p1 ** p3.
Proof.
  intros.
  sep_star_split_tac.
  simpls; simpljoin1.
 
  exists (m1, (r1, f2), d2) (merge m m2, (merge r r2, f2), d2).
  repeat (split; eauto).
  eapply disj_sep_merge_still; eauto.
  eapply disj_merge_disj_sep1 in H3.
  eapply disj_sym; eauto.
  
  eapply disj_sep_merge_still; eauto.
  eapply disj_merge_disj_sep1 in H4.
  eapply disj_sym; eauto.  
 
  rewrite merge_lift; eauto.
  assert (r ⊎ (r1 ⊎ r2) = r1 ⊎ (r ⊎ r2)).
  {
    rewrite merge_lift; eauto.
    eapply disj_merge_disj_sep1 in H4; eauto.
  }
  rewrite H5; eauto.
  eapply disj_merge_disj_sep1 in H3; eauto.

  exists (m, (r, f2), d2) (m2, (r2, f2), d2).
  simpl; eauto.
  repeat (split; eauto).
  eapply disj_merge_disj_sep2 in H3; eauto.
  eapply disj_merge_disj_sep2 in H4; eauto.
Qed.
    

(*+ Well-formed CodeHeap Proof +*)

Definition ins_sound_partial (p q : asrt) (i : ins) :=
  forall s s', s |= p -> (Q__ s (cntrans i) s') -> s' |= q.

Lemma total_to_partial :
  forall p q i,
    ins_sound p q i -> ins_sound_partial p q i.
Proof.
  intros.
  unfolds ins_sound, ins_sound_partial.
  intros.
  eapply H in H0; eauto.
  simpljoin1.
  eapply ins_exec_deterministic in H0; eauto.
  subst.
  eauto.
Qed.

Lemma pc_jmpl_npc_i_or_jmp :
  forall pc npc C aexp1 r1 I,
    LookupC C pc npc I ->
    C pc = Some (cjumpl aexp1 r1) ->
    (exists i, C npc = Some (cntrans i)) \/ (exists aexp2 r2, C npc = Some (cjumpl aexp2 r2)).
Proof.
  intros.
  inversion H; get_ins_diff_false.
  left.
  eauto.
  right.
  eauto.
Qed.

Lemma pc_be_npc_i :
  forall pc npc C aexp I,
    LookupC C pc npc I ->
    C pc = Some (cbe aexp) ->
    exists i, C npc = Some (cntrans i).
Proof.
  intros.
  inversion H; get_ins_diff_false.
  eauto.
Qed.

Lemma pc_bne_npc_i :
  forall pc npc C aexp I,
    LookupC C pc npc I ->
    C pc = Some (cbne aexp) ->
    exists i, C npc = Some (cntrans i).
Proof.
  intros.
  inversion H; get_ins_diff_false.
  eauto.
Qed.
  
(*+ progress +*)
Lemma seq_progress :
  forall p q S pc npc i C Spec I,
    wf_seq Spec p I q -> LookupC C pc npc I -> S |= p ->
    C pc = Some (cntrans i) ->
    exists S', P__ C (S, pc, npc) (S', npc, npc +ᵢ ($ 4)).
Proof.
  intros.
  generalize dependent C.
  generalize dependent pc.
  generalize dependent npc.
  generalize dependent i.
  generalize dependent S.
  induction H; intros; elim_ins_neq.

  -
    eapply ins_rule_sound in H.
    destruct_state S.
    assert (Hexe_dly : exists R' D', exe_delay r d = (R', D')).
    {
      eapply exe_delay_no_abort; eauto.
    }
    destruct Hexe_dly as [r' [d' Hexe_dly] ].
    symmetry in Hexe_dly.
    lets Hstep : Hexe_dly. 
    eapply dly_reduce_asrt_stable in Hstep; eauto.
    eapply H in Hstep; eauto. 
    simpljoin1.
    exists x.
    destruct_state x.
    econstructor; eauto.
    eapply NTrans; eauto.
    
  - 
    sep_star_split_tac.
    simpl in H9.
    simpljoin1.
    clear H5.
    eapply IHwf_seq in H1; eauto.
    destruct H1 as [S' H1].
    destruct_state S'.
    eapply program_step_safety_property with (s := (merge m m0, (merge r0 r1, f0), d0))
      in H1; eauto.
    simpljoin1; eauto.
    simpl.
    repeat (split; eauto).
    
  -
    simpl in H1.
    simpljoin1.
    eapply H0 in H1; eauto.

  -
    eapply H0 in H2.
    eauto.
Qed.

Lemma jmpl_progress1 :
  forall p q S pc npc aexp rd i C Spec I,
    wf_seq Spec p I q -> LookupC C pc npc I -> S |= p ->
    C pc = Some (cjumpl aexp rd) -> C npc = Some (cntrans i) ->
    exists S1 S2 pc1 pc2 npc1 npc2,
      P__ C (S, pc, npc) (S1, pc1, npc1) /\
      P__ C (S1, pc1, npc1) (S2, pc2, npc2).
Proof.
  intros.
  generalize dependent C.
  generalize dependent pc.
  generalize dependent npc.
  generalize dependent aexp.
  generalize dependent rd.
  generalize dependent i.
  generalize dependent S.

  induction H; intros; elim_ins_neq.

  -
    rewrite H8 in H15.
    inversion H15; subst.
    clear H15 H19.
    destruct_state S.
    assert (Hexe_dly1 : exists R' D', exe_delay r0 d = (R', D')).
    {
      eapply exe_delay_no_abort; eauto.
    }
    simpljoin1.
    renames x to R', x0 to D'.
    lets Hexe_dly1 : H10.
    symmetry in H10.
    eapply dly_reduce_asrt_stable in H10; eauto.
    lets Haexp : H10.
    eapply H in Haexp.
    simpl in Haexp.
    simpljoin1.
    lets Hjmp_step : H10.
    eapply H1 in Hjmp_step.
    assert (Hjmp_step1 : (m, (set_R R' r1 f1, f0), D') |= r1 |=> f1 ** p1).
    {
      clear - Hjmp_step.
      simpls.
      simpljoin1.
      destruct_state x.
      destruct_state x0.
      simpl in H.
      simpljoin1.
      unfolds regSt.
      simpls.
      simpljoin1.
      exists (empM, (set_R (RegMap.set r1 (Some v) empR) r1 f1, f2), d0) (m1, (r0, f2), d0).
      simpls.
      repeat (split; eauto).
      eapply disjoint_setR_still1; eauto.
      rewrite indom_setR_merge_eq1; eauto.
      eapply regset_l_l_indom; eauto.
      rewrite indom_setR_eq_RegMap_set; eauto.
      rewrite regset_twice; eauto.
      eapply regset_l_l_indom; eauto.
    }
    assert (Hexe_dly : exists R'' D'', exe_delay (set_R R' r1 f1) D' = (R'', D'')).
    {
      eapply exe_delay_no_abort; eauto.
    }
    simpljoin1.
    renames x to R'', x0 to D''.
    lets Hexe_dly2 : H13.
    lets Hi_step : Hjmp_step1.
    symmetry in H13. 
    eapply dly_reduce_asrt_stable in H13; eauto.
    lets Hi_step1 : H13. 
    eapply ins_rule_sound in H2.
    eapply H2 in Hi_step1; eauto.
    simpljoin1.
    exists (m, (set_R R' r1 f1, f0), D') x f2 f f (f +ᵢ ($ 4)).
    split.
    econstructor; eauto.
    eapply Jumpl; eauto.
    clear - Hjmp_step.
    sep_star_split_tac.
    simpls.
    unfolds regSt.
    simpls.
    simpljoin1.
    eapply indom_merge_still; eauto.
    eapply regset_l_l_indom; eauto.
    destruct_state x.
    econstructor; eauto.
    eapply NTrans; eauto.

  -
    sep_star_split_tac.
    simpl in H10.
    simpljoin1.
    rewrite H3 in H5.
    inversion H5; subst.
    clear H5.
    eapply IHwf_seq in H1; eauto.
    simpljoin1.
    renames x to s1, x1 to pc1, x3 to npc1.
    renames x0 to s2, x2 to pc2, x4 to npc2.
    destruct_state s1.
    eapply program_step_safety_property with (s := (merge m m0, (merge r0 r1, f0), d0))
      in H1; eauto.
    simpljoin1.
    destruct_state x0.
    simpl in H8.
    simpljoin1.
    eapply program_step_safety_property with (s := (merge m1 m2, (merge r2 r3, f1), d1))
      in H5; eauto.
    simpljoin1.
    destruct_state s2.
    destruct_state x0.
    simpl in H12.
    simpljoin1.
    exists (m1 ⊎ m2, (r2 ⊎ r3, f1), d1) (m3 ⊎ m4, (r4 ⊎ r5, f2), d2) pc1 pc2 npc1 npc2.
    split; eauto.
    simpl.
    repeat (split; eauto).
    simpl.
    repeat (split; eauto).

  -
    simpl in H1.
    simpljoin1.
    eapply H0 in H1; eauto.

  -
    eapply H0 in H2.
    eauto.
Qed.

Lemma jmpl_progress2 :
  forall p q S pc npc aexp1 aexp2 r1 r2 C Spec I,
    wf_seq Spec p I q -> LookupC C pc npc I -> S |= p ->
    C pc = Some (cjumpl aexp1 r1) -> C npc = Some (cjumpl aexp2 r2) ->
    exists S1 S2 pc1 pc2 npc1 npc2,
      P__ C (S, pc, npc) (S1, pc1, npc1) /\
      P__ C (S1, pc1, npc1) (S2, pc2, npc2).
Proof.
  intros.
  generalize dependent C.
  generalize dependent S.
  generalize dependent pc.
  generalize dependent npc.
  generalize dependent aexp1.
  generalize dependent aexp2.
  generalize dependent r1.
  generalize dependent r2.

  induction H; intros; elim_ins_neq.

  - 
    rewrite H9 in H16.
    inversion H16; subst.
    clear H16 H21.
    destruct_state S.
    assert (Hexe_dly1 : exists R' D', exe_delay r0 d = (R', D')).
    {
      eapply exe_delay_no_abort; eauto.
    }
    simpljoin1.
    renames x to R', x0 to D'.
    lets Hexe_delay1 : H11.
    symmetry in H11.
    eapply dly_reduce_asrt_stable in H11; eauto.
    lets Haexp1 : H11.
    eapply H in Haexp1.
    simpl in Haexp1.
    simpljoin1.
    assert (Hjmp_step1 : (m, (set_R R' r1 f1, f), D') |= r1 |=> f1 ** p1).
    {
      clear - H11 H0.
      eapply H0 in H11.
      sep_star_split_tac.
      simpl.
      simpl in H4.
      simpljoin1.
      exists (m0, (set_R r r1 f1, f2), d0) (m1, (r0, f2), d0).
      clear H0.
      simpls.
      unfolds regSt.
      simpls.
      simpljoin1.
      repeat (split; eauto).
      eapply disjoint_setR_still1; eauto.
      rewrite indom_setR_merge_eq1; eauto.
      eapply regset_l_l_indom; eauto.
      rewrite indom_setR_eq_RegMap_set; eauto.
      rewrite regset_twice; eauto.
      eapply regset_l_l_indom; eauto.
    }

    assert (Hexe_dly2 : exists R'' D'', exe_delay (set_R R' r1 f1) D' = (R'', D'')).
    {
      eapply exe_delay_no_abort; eauto.
    }
    simpljoin1.
    renames x to R'', x0 to D''.
    lets Hexe_delay2 : H14.
    symmetry in H14.
    eapply dly_reduce_asrt_stable in H14; eauto.
    lets Haexp2 : H14.
    eapply H1 in Haexp2.
    simpl in Haexp2.
    simpljoin1.
    eapply H2 in H14.
    assert (Hjmp_step2 : (m, (set_R R'' r2 f2, f), D'') |= r2 |=> f2 ** p2).
    {
      clear - H14.
      sep_star_split_tac.
      simpl in H3.
      simpljoin1.
      simpl.
      exists (m0, (set_R r r2 f2, f1), d0) (m1, (r0, f1), d0).
      simpls.
      unfolds regSt.
      simpls.
      simpljoin1.
      repeat (split; eauto).
      eapply disjoint_setR_still1; eauto.
      rewrite indom_setR_merge_eq1; eauto.
      eapply regset_l_l_indom; eauto.
      rewrite indom_setR_eq_RegMap_set; eauto.
      rewrite regset_twice; eauto.
      eapply regset_l_l_indom; eauto.
    }

    exists (m, (set_R R' r1 f1, f), D') (m, (set_R R'' r2 f2, f), D'') f2 f1' f1' f2'.
    split.
    econstructor; eauto.
    eapply Jumpl; eauto.  
    clear - H0 H11.
    eapply H0 in H11.
    sep_star_split_tac.
    simpls.
    unfolds regSt.
    simpls.
    simpljoin1.
    eapply indom_merge_still; eauto.
    eapply regset_l_l_indom; eauto.

    econstructor; eauto.
    eapply Jumpl; eauto.
    clear - H14.
    sep_star_split_tac.
    simpls.
    unfolds regSt.
    simpls.
    simpljoin1.
    eapply indom_merge_still; eauto.
    eapply regset_l_l_indom; eauto.

  -
    sep_star_split_tac.
    simpl in H10.
    simpljoin1.
    rewrite H3 in H5.
    inversion H5; subst.
    clear H5.
    eapply IHwf_seq in H1; eauto.
    simpljoin1.
    eapply program_step_safety_property with (s := (merge m m0, (merge r0 r2, f0), d0))
      in H1; eauto.
    simpljoin1.
    destruct_state x.
    destruct_state x6.
    simpl in H8.
    simpljoin1.
    eapply program_step_safety_property with (s := (merge m1 m2, (merge r1 r3, f1), d1))
      in H5; eauto.
    simpljoin1.
    destruct_state x0.
    destruct_state x5.
    simpl in H12.
    simpljoin1.
    exists (m1 ⊎ m2, (r1 ⊎ r3, f1), d1) (m3 ⊎ m4, (r4 ⊎ r5, f2), d2)
      x1 x2 x3 x4.
    split; eauto.
    simpl.
    repeat (split; eauto).
    simpl.
    repeat (split; eauto).

  -
    rewrite H3 in H5.
    inversion H5; subst.
    clear H5 H6.
    simpl in H1.
    simpljoin1.
    eauto.

  -
    eapply H0 in H2.
    eauto.
Qed.

Lemma be_progress :
  forall p q S pc npc aexp C Spec I,
    wf_seq Spec p I q -> LookupC C pc npc I -> S |= p ->
    C pc = Some (cbe aexp) ->
    exists S1 S2 pc1 pc2 npc1 npc2,
      P__ C (S, pc, npc) (S1, pc1, npc1) /\
      P__ C (S1, pc1, npc1) (S2, pc2, npc2).
Proof.
  intros.
  generalize dependent C.
  generalize dependent S.
  generalize dependent pc.
  generalize dependent npc.
  generalize dependent aexp.

  induction H; intros; elim_ins_neq.

  -
    clear H15.
    destruct_state S.
    assert (Hexe_dly1 : exists R' D', exe_delay r0 d = (R', D')).
    {
      eapply exe_delay_no_abort; eauto.
    }
    simpljoin1.
    renames x to R', x0 to D'.
    lets Hexe_delay1 : H9.
    symmetry in H9.
    eapply dly_reduce_asrt_stable in H9; eauto.
    lets Haexp : H9.
    eapply H in Haexp.
    simpl in Haexp.
    simpljoin1.
    assert (Hexe_delay2 : exists R'' D'', exe_delay R' D' = (R'', D'')).
    {
      eapply exe_delay_no_abort; eauto.
    }
    simpljoin1.
    renames x to R'', x0 to D''.
    lets Hexe_delay2 : H12.
    symmetry in H12.
    eapply dly_reduce_asrt_stable in H12; eauto.
    eapply ins_rule_sound in H1.
    eapply H1 in H12.
    simpljoin1.
    destruct (Int.eq bv ($ 0)) eqn:Heqe.
    {   
      exists (m, (R', f0), D') x f2 (f2 +ᵢ ($ 4)) (f2 +ᵢ ($ 4)) ((f2 +ᵢ ($ 4)) +ᵢ ($ 4)).
      split. 
      econstructor; eauto.
      eapply Be_false; eauto.
      eapply H2 in H9.
      clear - H9 Heqe.
      simpl in H9.
      unfolds regSt.
      simpls.
      simpljoin1.
      destruct_state x.
      destruct_state x0.
      simpls.
      simpljoin1.
      unfold merge.
      unfold RegMap.set.
      destruct_rneq.
      clear - Heqe.
      unfolds Int.eq.
      destruct (zeq (Int.unsigned bv) (Int.unsigned $ 0)); tryfalse.
      eapply z_eq_to_int_eq in e.
      do 2 rewrite Int.repr_unsigned in e.
      inversion e; subst; eauto.
      destruct_state x. 
      econstructor; eauto.
      eapply NTrans; eauto.
    }
    {
      exists (m, (R', f0), D') x f2 f f (f +ᵢ ($ 4)).
      split.
      econstructor; eauto.
      eapply Be_true; eauto.
      instantiate (1 := bv).
      eapply H2 in H9.
      clear - H9.
      sep_star_split_tac.
      simpl in H3.
      simpljoin1.
      simpl in H1.
      unfolds regSt.
      simpls.
      simpljoin1.
      unfold merge.
      unfold RegMap.set.
      destruct_rneq.
      clear - Heqe.
      unfolds Int.eq.
      intro.
      destruct (zeq (Int.unsigned bv) (Int.unsigned $ 0)) eqn:Heqe1; tryfalse.
      destruct_state x.
      econstructor; eauto.
      eapply NTrans; eauto.
    }

  -
    clear H4.
    sep_star_split_tac.
    simpl in H9.
    simpljoin1.
    eapply IHwf_seq in H1; eauto.
    simpljoin1.
    destruct_state x.
    destruct_state x0. 
    eapply program_step_safety_property with (s := (merge m m0, (merge r0 r1, f0), d0))
      in H1; eauto.
    simpljoin1.
    destruct_state x0.
    simpl in H10.
    simpljoin1.
    eapply program_step_safety_property with (s := (merge m1 m3, (merge r2 r4, f2), d2))
      in H9; eauto.
    simpljoin1.
    destruct_state x0.
    simpl in H13.
    simpljoin1. 
    exists (m1 ⊎ m3, (r2 ⊎ r4, f2), d2) (m2 ⊎ m4, (r3 ⊎ r5, f), d)
      x1 x2 x3 x4.
   split; eauto.
   simpl; eauto.
   simpl; eauto.

  -
    simpl in H1.
    simpljoin1.
    eauto.

  -
    eapply H0 in H2.
    eauto.
Qed.

Lemma bne_progress :
  forall p q S pc npc aexp C Spec I,
    wf_seq Spec p I q -> LookupC C pc npc I -> S |= p ->
    C pc = Some (cbne aexp) ->
    exists S1 S2 pc1 pc2 npc1 npc2,
      P__ C (S, pc, npc) (S1, pc1, npc1) /\
      P__ C (S1, pc1, npc1) (S2, pc2, npc2).
Proof.
  intros.
  generalize dependent C.
  generalize dependent S.
  generalize dependent pc.
  generalize dependent npc.
  generalize dependent aexp.

  induction H; intros; elim_ins_neq.

  -
    clear H15.
    destruct_state S.
    assert (Hexe_dly1 : exists R' D', exe_delay r0 d = (R', D')).
    {
      eapply exe_delay_no_abort; eauto.
    }
    simpljoin1.
    renames x to R', x0 to D'.
    lets Hexe_delay1 : H9.
    symmetry in H9.
    eapply dly_reduce_asrt_stable in H9; eauto.
    lets Haexp : H9.
    eapply H in Haexp.
    simpl in Haexp.
    simpljoin1.
    assert (Hexe_delay2 : exists R'' D'', exe_delay R' D' = (R'', D'')).
    {
      eapply exe_delay_no_abort; eauto.
    }
    simpljoin1.
    renames x to R'', x0 to D''.
    lets Hexe_delay2 : H12.
    symmetry in H12.
    eapply dly_reduce_asrt_stable in H12; eauto.
    eapply ins_rule_sound in H1.
    eapply H1 in H12.
    simpljoin1.
    destruct (Int.eq bv ($ 0)) eqn:Heqe.
    { 
      exists (m, (R', f0), D') x f2 f f (f +ᵢ ($ 4)).
      split.  
      econstructor; eauto.
      eapply Bne_true; eauto.
      eapply H2 in H9.
      clear - H9 Heqe.
      sep_star_split_tac.
      simpls.
      simpljoin1.
      unfolds regSt.
      simpls.
      simpljoin1.
      unfold merge.
      unfold RegMap.set.
      destruct_rneq.
      clear - Heqe.
      unfolds Int.eq.
      destruct (zeq (Int.unsigned bv) (Int.unsigned $ 0)); tryfalse.
      eapply z_eq_to_int_eq in e; eauto.
      do 2 rewrite Int.repr_unsigned in e.
      subst.
      eauto.
      destruct_state x.
      econstructor; eauto.
      eapply NTrans; eauto.
    }
    {
      exists (m, (R', f0), D') x f2 (f2 +ᵢ ($ 4)) (f2 +ᵢ ($ 4)) ((f2 +ᵢ ($ 4)) +ᵢ ($ 4)).
      split.
      econstructor; eauto.
      eapply Bne_false; eauto.
      instantiate (1 := bv).
      eapply H2 in H9.
      clear - H9 Heqe.
      simpl in H9.
      unfolds regSt.
      simpls.
      simpljoin1.
      destruct_state x.
      destruct_state x0.
      simpls.
      simpljoin1.
      unfold merge.
      unfold RegMap.set.
      destruct_rneq.
      clear - Heqe.
      unfolds Int.eq.
      destruct (zeq (Int.unsigned bv) (Int.unsigned $ 0)); tryfalse.
      intro.
      subst.
      eapply n.
      simpl; eauto.
      destruct_state x. 
      econstructor; eauto.
      eapply NTrans; eauto.
    }

  -
    clear H4.
    sep_star_split_tac.
    simpl in H9.
    simpljoin1.
    eapply IHwf_seq in H1; eauto.
    simpljoin1.
    destruct_state x.
    destruct_state x0. 
    eapply program_step_safety_property with (s := (merge m m0, (merge r0 r1, f0), d0))
      in H1; eauto.
    simpljoin1.
    destruct_state x0.
    simpl in H10.
    simpljoin1.
    eapply program_step_safety_property with (s := (merge m1 m3, (merge r2 r4, f2), d2))
      in H9; eauto.
    simpljoin1.
    destruct_state x0.
    simpl in H13.
    simpljoin1. 
    exists (m1 ⊎ m3, (r2 ⊎ r4, f2), d2) (m2 ⊎ m4, (r3 ⊎ r5, f), d)
      x1 x2 x3 x4.
   split; eauto.
   simpl; eauto.
   simpl; eauto.

  -
    simpl in H1.
    simpljoin1.
    eauto.

  -
    eapply H0 in H2.
    eauto.
Qed.

Lemma retl_progress :
  forall p q S pc npc C I Spec,
    wf_seq Spec p I q -> LookupC C pc npc I -> S |= p ->
    C pc = Some (cretl) ->
    exists S1 S2 pc1 pc2 npc1 npc2,
      P__ C (S, pc, npc) (S1, pc1, npc1) /\
      P__ C (S1, pc1, npc1) (S2, pc2, npc2).
Proof.
  intros.
  generalize dependent C.
  generalize dependent S.
  generalize dependent pc.
  generalize dependent npc.

  induction H; intros; elim_ins_neq.

  - 
    clear H10.
    destruct_state S.
    assert (Hexe_dly1 : exists R' D', exe_delay r d = (R', D')).
    {
      eapply exe_delay_no_abort; eauto.
    }
    simpljoin1.
    renames x to R', x0 to D'.
    lets Hexe_delay1 : H5.
    symmetry in H5.
    eapply dly_reduce_asrt_stable in H5; eauto.
    assert (Hexe_dly2 : exists R'' D'', exe_delay R' D' = (R'', D'')).
    {
      eapply exe_delay_no_abort; eauto.
    }
    simpljoin1.
    renames x to R'', x0 to D''.
    lets Hexe_delay2 : H6.
    symmetry in H6.
    eapply dly_reduce_asrt_stable in H6; eauto.
    eapply ins_rule_sound in H.
    lets Hp' : H6.
    eapply H in Hp'; eauto.
    simpljoin1.
    destruct_state x.
    unfolds fretSta.
    lets Hret_f : H6.
    eapply H1 in Hret_f; eauto.
    simpljoin1.
    simpls.  
    exists (m, (R', f), D') (m0, (r0, f0), d0) f2 (x +ᵢ ($ 8)) (x +ᵢ ($ 8)) (x +ᵢ ($ 12)).
    split. 
    econstructor; eauto.
    eapply Retl; eauto.
    eapply exe_delay_general_reg_stable in H9; eauto.
    econstructor; eauto.
    assert (x +ᵢ ($ 12) = (x +ᵢ ($ 8)) +ᵢ ($ 4)).
    {
      rewrite Int.add_assoc; eauto.
    }
    rewrite H11; eauto.
    eapply NTrans; eauto.

  -
    sep_star_split_tac.
    simpl in H9.
    simpljoin1.
    eapply IHwf_seq in H1; eauto.
    simpljoin1.
    destruct_state x.
    destruct_state x0.
    eapply program_step_safety_property with (s := (merge m m0, (merge r0 r1, f0), d0))
      in H1; eauto.
    simpljoin1.
    destruct_state x0.
    simpl in H9.
    simpljoin1.
    eapply program_step_safety_property with (s := (merge m1 m3, (merge r2 r4, f2), d2))
      in H7; eauto.
    simpljoin1.
    exists (m1 ⊎ m3, (r2 ⊎ r4, f2), d2) x x1 x2 x3 x4.
    split; eauto.
    simpl; eauto.
    simpl; eauto.

  -
    simpl in H1.
    simpljoin1.
    eauto.

  -
    eapply H0 in H2.
    eauto.
Qed.

Lemma call_progress :
  forall p q S pc npc C I Spec f,
    wf_seq Spec p I q -> LookupC C pc npc I -> S |= p ->
    C pc = Some (ccall f) ->
    exists S1 S2 pc1 pc2 npc1 npc2,
      P__ C (S, pc, npc) (S1, pc1, npc1) /\
      P__ C (S1, pc1, npc1) (S2, pc2, npc2).
Proof.
  intros.
  generalize dependent C.
  generalize dependent S.
  generalize dependent pc.
  generalize dependent npc.

  induction H; intros; elim_ins_neq.

  -
    clear H18.
    destruct_state S.
    assert (Hexe_dly1 : exists R' D', exe_delay r0 d = (R', D')).
    {
      eapply exe_delay_no_abort; eauto.
    }
    simpljoin1.
    renames x to R', x0 to D'.
    lets Hexe_delay1 : H11.
    symmetry in H11.
    eapply dly_reduce_asrt_stable in H11; eauto.
    lets Hr15 : H11.
    eapply H0 in Hr15.
    assert (Hr15' : (m, (set_R R' r15 f1, f), D') |= r15 |=> f1 ** p1).
    {
      clear - Hr15.
      sep_star_split_tac.
      simpls.
      simpljoin1.
      unfolds regSt.
      simpls.
      simpljoin1.
      exists (empM, (set_R (RegMap.set r15 (Some v) empR) r15 f1, f2), d0)
        (m1, (r0, f2), d0).
      simpls.
      repeat (split; eauto).
      eapply disjoint_setR_still1; eauto.
      rewrite indom_setR_merge_eq1; eauto.
      eapply regset_l_l_indom; eauto.
      rewrite indom_setR_eq_RegMap_set; eauto.
      rewrite regset_twice; eauto.
      eapply regset_l_l_indom; eauto.
    }
    
    assert (Hexe_dly2 : exists R'' D'', exe_delay (set_R R' r15 f1) D' = (R'', D'')).
    {
      eapply exe_delay_no_abort; eauto.
    }
    simpljoin1.
    renames x to R'', x0 to D''.
    lets Hexe_delay2 : H12.
    symmetry in H12. 
    eapply dly_reduce_asrt_stable in H12; eauto.
    eapply ins_rule_sound in H1.
    eapply H1 in H12.
    simpljoin1.  
    exists (m, (set_R R' r15 f1, f), D') x (f1 +ᵢ ($ 4)) f0 f0 (f0 +ᵢ ($ 4)).
    split.
    econstructor; eauto.
    eapply Call; eauto.
    clear - Hr15.
    sep_star_split_tac.
    simpls.
    simpljoin1.
    unfolds regSt.
    simpls.
    simpljoin1.
    eapply indom_merge_still; eauto.
    eapply regset_l_l_indom; eauto.
    destruct_state x.
    econstructor; eauto.
    eapply NTrans; eauto.

  -
    sep_star_split_tac.
    simpls.
    simpljoin1.
    eapply IHwf_seq in H1; eauto.
    simpljoin1.
    destruct_state x.
    destruct_state x0.
    eapply program_step_safety_property with (s := (merge m m0, (merge r0 r1, f1), d0))
      in H1; eauto.
    simpljoin1.
    destruct_state x0.
    simpls.
    simpljoin1.
    eapply program_step_safety_property with (s := (merge m1 m3, (merge r2 r4, f3), d2))
      in H8; eauto.
    simpljoin1.
    destruct_state x0.
    simpls.
    simpljoin1.
    exists (m1 ⊎ m3, (r2 ⊎ r4, f3), d2) (m2 ⊎ m4, (r3 ⊎ r5, f), d) x1 x2 x3 x4.
    split; eauto.
    simpl; eauto.
    simpl; eauto.

  -
    simpls.
    simpljoin1.
    eauto.

  -
    eauto.
Qed.
    
(*+ preservation +*)
Lemma seq_preservation :
  forall p q S S' pc pc' npc npc' i C Spec I,
    wf_seq Spec p I q -> LookupC C pc npc I -> S |= p ->
    C pc = Some (cntrans i) -> P__ C (S, pc, npc) (S', pc', npc') ->
    exists p' I', S' |= p' /\ LookupC C pc' npc' I' /\ wf_seq Spec p' I' q.
Proof.
  intros.
  generalize dependent C.
  generalize dependent S.
  generalize dependent S'.
  generalize dependent pc.
  generalize dependent pc'.
  generalize dependent npc.
  generalize dependent npc'.
  generalize dependent i.

  induction H; intros; elim_ins_neq. 
  - 
    inversion H4; subst.
    eapply dly_reduce_asrt_stable in H8; eauto.
    eapply ins_rule_sound in H.
    eapply total_to_partial in H.
    inversion H15; get_ins_diff_false.
    eapply H in H8; eauto.
    eapply H8 in H17.
    clear H8 H15.
    exists p' I.
    repeat (split; eauto).
  -   
    sep_star_split_tac.
    simpl in H10.
    simpljoin1.
    eapply seq_progress in H; eauto.
    destruct H as [s' H].
    inversion H4; subst.
    inversion H20; get_ins_diff_false.
    eapply IHwf_seq in H1; eauto.
    simpljoin1.  
    renames x to p', x0 to I0'.
    exists (p' ** r) I0'.
    eapply program_step_safety_property with
    (s := (merge m m0, (merge r0 r1, f0), d0)) (r := r) in H; eauto.
    simpljoin1.
    eapply program_step_deterministic in H4; eauto.
    simpljoin1.
    destruct_state s'.
    destruct_state x0.
    simpl in H11.
    simpljoin1.
    repeat (split; eauto).
    simpl.
    exists (m1, (r2, f1), d1) (m2, (r3, f1), d1).
    repeat (split; eauto).
    eapply Seq_frame_rule in H10; eauto.
    simpl.
    repeat (split; eauto).
  -
    simpl in H1.
    simpljoin1.
    eauto.
  -
    eapply H0 in H2.
    eapply IHwf_seq in H2; eauto.
    simpljoin1. 
    eapply Seq_conseq_rule with (p := x) (q := q) in H9; eauto.
Qed.

Lemma jmpl_preservation1 :
  forall p q S S1 S2 aexp rd pc pc1 pc2 npc npc1 npc2 Spec Spec' C i I,
    wf_seq Spec p I q -> LookupC C pc npc I -> S |= p ->
    wf_cdhp Spec C Spec' -> cdhp_subst Spec Spec' ->
    C pc = Some (cjumpl aexp rd) -> C npc = Some (cntrans i) ->
    P__ C (S, pc, npc) (S1, pc1, npc1) -> P__ C (S1, pc1, npc1) (S2, pc2, npc2) ->
    exists I' fp fq L r,
      wf_seq Spec (fp L ** r) I' (fq L ** r) /\ LookupC C pc2 npc2 I' /\ DlyFrameFree r /\
      Spec (pc2, npc2) = Some (fp, fq) /\ S2 |= (fp L ** r) /\ fq L ** r ==> q.
Proof.
  intros.
  generalize dependent C.
  generalize dependent pc.
  generalize dependent pc1.
  generalize dependent pc2.
  generalize dependent npc.
  generalize dependent npc1.
  generalize dependent npc2.
  generalize dependent S.
  generalize dependent S1.
  generalize dependent S2.
  generalize dependent aexp.
  generalize dependent i.

  induction H; intros; elim_ins_neq.
 
  -
    rewrite H10 in H19.
    inversion H19; subst.
    clear H19 H23.
    inversion H12; subst.
    inversion H22; get_ins_diff_false.
    clear H12 H22.
    eapply dly_reduce_asrt_stable in H17; eauto.
    lets Haexp : H17.
    eapply H in Haexp.
    simpl in Haexp.
    simpljoin1.
    rewrite H30 in H12.
    inversion H12; subst.
    clear H12 H14.
    lets Hspec : H0.
    unfold cdhp_subst in H3.
    eapply H3 in H0.
    unfold wf_cdhp in H9. 
    eapply H9 with (L := L) in H0.
    simpljoin1.
    rename x into I'.
    inversion H13; subst.
    inversion H26; get_ins_diff_false.
    eapply H1 in H17.
    assert ((M', (set_R R' rd f1, F'), D'') |= rd |=> f1 ** p1).
    {
      clear - H17.
      simpls.
      simpljoin1.
      destruct_state x.
      destruct_state x0.
      unfolds regSt.
      simpls.
      simpljoin1.
      do 2 eexists.
      repeat (split; eauto).
      instantiate (1 := (empM, (set_R (RegMap.set rd (Some v) empR) rd f1, f0), d0)).
      simpl.
      repeat (split; eauto).
      eapply disjoint_setR_still1; eauto.
      rewrite indom_setR_merge_eq1; eauto.
      eapply regset_l_l_indom; eauto.
      simpl.
      rewrite indom_setR_eq_RegMap_set; eauto.
      rewrite regset_twice; eauto.
      eapply regset_l_l_indom; eauto.
      simpl; eauto.
    }
    exists I' fp fq L r.
    eapply Seq_frame_rule with (r := r) in H12; eauto. 
    repeat (split; eauto).
    eapply dly_reduce_asrt_stable in H18; eauto.
    eapply ins_rule_sound in H2.
    eapply total_to_partial in H2.
    eapply H2 in H18; eauto.

  - 
    sep_star_split_tac.
    simpl in H14.
    simpljoin1.
    rewrite H5 in H9.
    inversion H9; subst.
    eapply jmpl_progress1 in H; eauto.
    simpljoin1.
    eapply IHwf_seq in H1; eauto.
    simpljoin1.
    renames x6 to fp, x7 to fq, x8 to L, x9 to r', x5 to I'.
    eapply program_step_safety_property with
    (s := (merge m m0, (merge r0 r1, f0), d0)) (r := r) in H; eauto. 
    simpljoin1. 
    eapply program_step_deterministic in H7; eauto.
    simpljoin1; subst.
    destruct_state x.
    destruct_state x6.
    simpl in H18.
    simpljoin1; eauto.
    eapply program_step_safety_property with
    (s := (merge m1 m2, (merge r2 r3, f1), d1)) (r := r) in H12; eauto.
    simpljoin1. 
    destruct_state x0.
    destruct_state x1.
    simpl in H20.
    simpljoin1.
    eapply program_step_deterministic in H8; eauto.
    simpljoin1. 
    exists I' fp fq L (r' ** r).
    repeat (split; eauto).
    eapply Seq_frame_rule with (r := r) in H1; eauto.
    eapply Seq_conseq_rule with (p := fp L ** r' ** r) (q := fq L ** r' ** r) in H1.
    Focus 2.
    clear.
    intros.
    eapply sep_star_assoc; eauto.
    Focus 2.
    clear.
    intros.
    eapply sep_star_assoc2; eauto.
    eauto.  
    clear - H21 H16 H20 H22.
    eapply sep_star_assoc2.
    simpls. 
    simpljoin1.
    destruct_state x.
    destruct_state x0.
    simpl in H.
    simpljoin1.
    do 2 eexists. 
    repeat (split; eauto).
    Focus 2.
    do 2 eexists.
    repeat (split; eauto).
    simpl.
    repeat (split; eauto).
    intros.
    clear - H17 H8.
    eapply sep_star_assoc in H8.
    eapply sep_star_split in H8.
    simpljoin1.
    destruct_state x.
    destruct_state x0.
    simpl in H1.
    simpljoin1.
    eapply H17 in H.
    simpl.
    do 2 eexists.
    repeat (split; eauto).

    simpl.
    repeat (split; eauto).
    simpl.
    repeat (split; eauto).

  -
    simpl in H1.
    simpljoin1.
    eapply H0 in H1; eauto.

  -
    eapply H0 in H2.
    eapply IHwf_seq in H2; eauto.
    simpljoin1.
    renames x0 to fp, x1 to fq, x2 to L, x3 to r, x to I.
    exists I fp fq L r.
    repeat (split; eauto).
Qed.

Lemma jmpl_preservation2 :
  forall p q S S1 S2 aexp1 aexp2 r1 r2 pc pc1 pc2 npc npc1 npc2 Spec Spec' C I,
    wf_seq Spec p I q -> LookupC C pc npc I -> S |= p ->
    wf_cdhp Spec C Spec' -> cdhp_subst Spec Spec' ->
    C pc = Some (cjumpl aexp1 r1) -> C npc = Some (cjumpl aexp2 r2) ->
    P__ C (S, pc, npc) (S1, pc1, npc1) -> P__ C (S1, pc1, npc1) (S2, pc2, npc2) ->
    exists I' fp fq L r,
      wf_seq Spec (fp L ** r) I' (fq L ** r) /\ LookupC C pc2 npc2 I' /\ DlyFrameFree r /\
      Spec (pc2, npc2) = Some (fp, fq) /\ S2 |= (fp L ** r) /\ fq L ** r ==> q.
Proof.
  intros.
  generalize dependent C.
  generalize dependent S.
  generalize dependent S1.
  generalize dependent S2.
  generalize dependent pc.
  generalize dependent pc1.
  generalize dependent pc2.
  generalize dependent npc.
  generalize dependent npc1.
  generalize dependent npc2.
  generalize dependent aexp1.
  generalize dependent aexp2.

  induction H; intros; elim_ins_neq.

  -
    inversion H13; subst.
    lets Hexe_dly1 : H18.
    eapply dly_reduce_asrt_stable in H18; eauto.
    clear H25.
    inversion H24; get_ins_diff_false.
    lets Haexp : H18.
    eapply H in Haexp.
    simpl in Haexp.
    simpljoin1.
    rewrite H32 in H15.
    inversion H15; subst.
    clear H15 H16.
    inversion H14; subst.
    lets Hexe_dly2 : H19.
    eapply H0 in H18.
    assert (Hp1 : (M', (set_R R' rd f1, F'), D'') |= rd |=> f1 ** p1).
    {
      clear - H18.
      simpls.
      simpljoin1.
      destruct_state x.
      destruct_state x0.
      unfolds regSt.
      simpls.
      simpljoin1.
      exists (empM, (set_R (RegMap.set rd (Some v1) empR) rd f1, f0), d0) (m0, (r0, f0), d0).
      simpls.
      repeat (split; eauto).
      eapply disjoint_setR_still1; eauto.
      rewrite indom_setR_merge_eq1; eauto.
      eapply regset_l_l_indom; eauto.
      rewrite indom_setR_eq_RegMap_set; eauto.
      rewrite regset_twice; eauto.
      eapply regset_l_l_indom; eauto.
    }
    eapply dly_reduce_asrt_stable in H19; eauto.
    lets Haexp2 : H19.
    eapply H1 in Haexp2.
    simpl in Haexp2.
    simpljoin1.
    inversion H29; get_ins_diff_false.
    rewrite H39 in H15.
    inversion H15; subst.
    clear H15 H16.
    lets Hwf_cdhp : H10.
    lets Hcdhp_subst : H3.
    unfold cdhp_subst in Hcdhp_subst.
    lets Hspec : H4.
    eapply Hcdhp_subst in Hspec.
    unfold wf_cdhp in Hwf_cdhp. 
    eapply Hwf_cdhp with (L := L) in Hspec.
    simpljoin1.
    rename x into I'.
    eapply Seq_frame_rule with (r := r) in H16; eauto.
    exists I' fp fq L r.
    repeat (split; eauto).
    eapply H2 in H19.
    clear - H19 H5.
    assert ((M'0, (set_R R'0 rd0 pc1, F'0), D''0) |= rd0 |=> pc1 ** p2).
    {
      sep_star_split_tac.
      simpl in H3.
      simpljoin1.
      clear H5.
      simpls.
      unfolds regSt.
      simpls.
      exists (m, (set_R r0 rd0 pc1, f0), d0) (m0, (r1, f0), d0).
      simpljoin1.
      simpl.
      repeat (split; eauto).
      eapply disjoint_setR_still1; eauto.
      rewrite indom_setR_merge_eq1; eauto.
      eapply regset_l_l_indom; eauto.
      rewrite indom_setR_eq_RegMap_set; eauto.
      rewrite regset_twice; eauto.
      eapply regset_l_l_indom; eauto.
    }
    eauto.

  -
    rewrite H5 in H9.
    inversion H9; subst.
    clear H9 H10.
    sep_star_split_tac.
    simpl in H12.
    simpljoin1.
    eapply jmpl_progress2 in H; eauto.
    simpljoin1.
    lets Hstep1 : H.
    eapply program_step_safety_property
    with (s := (merge m m0, (merge r0 r1, f0), d0)) in Hstep1; eauto.
    simpljoin1.
    destruct_state x.
    destruct_state x6.
    simpl in H14.
    simpljoin1.
    lets Hstep2 : H12.
    eapply program_step_safety_property
    with (s := (merge m1 m2, (merge r2 r3, f1), d1)) in Hstep2; eauto.
    simpljoin1.
    destruct_state x0.
    destruct_state x5.
    simpl in H18.
    simpljoin1.
    eapply program_step_deterministic in H7; eauto.
    simpljoin1.
    eapply program_step_deterministic in H8; eauto.
    simpljoin1.
    eapply IHwf_seq in H1; eauto.
    simpljoin1.
    renames x0 to fp, x1 to fq, x2 to L, x3 to r', x to I'.
    exists I' fp fq L (r' ** r).
    repeat (split; eauto).

    eapply Seq_frame_rule with (r := r) in H1.
    eapply Seq_conseq_rule in H1; eauto.
    intros.
    eapply sep_star_assoc; eauto.
    intros.
    eapply sep_star_assoc2; eauto.
    eauto.

    clear - H18 H20 H19 H22.
    eapply sep_star_assoc2; eauto.
    eapply disj_sep_star_merge; eauto.

    clear - H23.
    intros.
    eapply sep_star_assoc in H.
    eapply sep_star_split in H; eauto.
    simpljoin1.
    destruct_state x.
    destruct_state x0.
    simpl in H1; simpljoin1.
    eapply H23 in H.
    eapply disj_sep_star_merge; eauto.

    simpl.
    repeat (split; eauto).

    simpl.
    repeat (split; eauto).

  -
    simpl in H1.
    simpljoin1.
    eauto.

  -
    eapply H0 in H2.
    eapply IHwf_seq in H2; eauto.
    simpljoin1.
    do 5 eexists.
    repeat (split; eauto).
Qed.

Lemma be_preservation :
  forall p q S S1 S2 aexp pc npc pc1 npc1 pc2 npc2 Spec Spec' C i I,
     wf_seq Spec p I q -> LookupC C pc npc I -> S |= p ->
     wf_cdhp Spec C Spec' -> cdhp_subst Spec Spec' ->
     C pc = Some (cbe aexp) -> C npc = Some (cntrans i) ->
     P__ C (S, pc, npc) (S1, pc1, npc1) -> P__ C (S1, pc1, npc1) (S2, pc2, npc2) ->
     exists I' p',
       wf_seq Spec p' I' q /\ LookupC C pc2 npc2 I' /\ S2 |= p'.
Proof.
  intros.
  generalize dependent C.
  generalize dependent S.
  generalize dependent S1.
  generalize dependent S2.
  generalize dependent aexp.
  generalize dependent pc.
  generalize dependent pc1.
  generalize dependent pc2.
  generalize dependent npc.
  generalize dependent npc1.
  generalize dependent npc2.
  generalize dependent i.

  induction H; intros; elim_ins_neq.

  -
    inversion H12; subst.
    rewrite H10 in H20.
    inversion H20; subst.
    inversion H25; get_ins_diff_false.

    clear H23 H22 H20.
    eapply dly_reduce_asrt_stable in H17; eauto.
    lets Hz : H17.
    eapply H2 in Hz.
    assert (bv = v).
    {
      clear - Hz H34.
      sep_star_split_tac.
      simpl in H3.
      simpljoin1.
      simpl in H1.
      unfolds regSt.
      simpls.
      simpljoin1.
      clear - H34.
      unfold merge in *.
      unfolds RegMap.set.
      destruct_rneq_H.
      inversion H34; eauto.
    }
    subst.

    inversion H13; subst.
    eapply dly_reduce_asrt_stable with (p := p ↓) in H18; eauto.
    eapply ins_rule_sound in H1.
    eapply total_to_partial in H1.
    inversion H28; get_ins_diff_false.
    eapply H1 in H18; eauto.
    eapply H18 in H26; eauto.
    clear H18.
    assert (Hfalse : v =ᵢ ($ 0) = false).
    {
      clear - H35.
      unfold Int.eq.
      destruct (zeq (Int.unsigned v) (Int.unsigned $ 0)) eqn:Heqe; eauto.
      clear Heqe.
      eapply z_eq_to_int_eq in e; eauto.
      do 2 rewrite Int.repr_unsigned in e.
      subst.
      tryfalse.
    }
    eapply H6 in Hfalse.
    lets Hspec : H0.
    unfold cdhp_subst in H3.
    eapply H3 in Hspec.
    unfold wf_cdhp in H9.
    eapply H9 with (L := L) in Hspec; eauto.
    simpljoin1.
    rename x into I'.
    eapply Seq_frame_rule with (r := r) in H15; eauto.
    eapply H in H17.
    simpl in H17.
    simpljoin1.
    rewrite H17 in H33.
    inversion H33; subst.
    exists I' (fp L ** r).
    repeat (split; eauto).
    eapply Seq_conseq_rule; eauto.

    clear H20 H21 H23.
    eapply dly_reduce_asrt_stable in H17; eauto.
    inversion H13; subst.
    eapply dly_reduce_asrt_stable in H18; eauto.
    inversion H28; get_ins_diff_false.
    eapply ins_rule_sound in H1.
    eapply total_to_partial in H1.
    eapply H1 in H18.
    eapply H18 in H26; eauto.
    clear H18.
    exists I (p' //\\ [|bv =ᵢ ($ 0) = true|]).
    repeat (split; eauto).
    assert ((pc1 +ᵢ ($ 4)) +ᵢ ($ 4) = pc1 +ᵢ ($ 8)).
    {
      rewrite Int.add_assoc; eauto.
    }
    rewrite H14; eauto.
    clear - H34 H2 H17.
    eapply H2 in H17.
    sep_star_split_tac.
    simpl in H4.
    simpljoin1.
    clear - H34 H1.
    simpl in H1.
    unfolds regSt.
    simpls.
    simpljoin1.
    unfold merge in *.
    unfolds RegMap.set.
    destruct_rneq_H.
    inversion H34; eauto.

  -
    rewrite H5 in H9.
    inversion H9; subst.
    clear H9 H10.
    sep_star_split_tac.
    simpl in H13.
    simpljoin1.
    eapply be_progress in H; eauto.
    simpljoin1.
    destruct_state x.
    destruct_state x0.
    eapply IHwf_seq in H1; eauto.
    destruct H1 as [ I' [p' H1] ].
    simpljoin1. 
    eapply program_step_safety_property with (s := (merge m m0, (merge r0 r1, f0), d0)) (r := r)
      in H; eauto.
    simpljoin1.
    destruct_state x0.
    simpl in H16.
    simpljoin1.
    eapply program_step_safety_property with (s := (merge m1 m3, (merge r2 r4, f2), d2)) (r := r)
      in H13; eauto.
    simpljoin1.
    destruct_state x0.
    simpl in H19.
    simpljoin1.
    eapply program_step_deterministic in H7; eauto.
    simpljoin1.
    eapply program_step_deterministic in H8; eauto.
    simpljoin1.
    exists I' (p' ** r).
    repeat (split; eauto).
    eapply Seq_frame_rule; eauto.
    clear - H19 H21 H20 H15.
    simpl.
    do 2 eexists.
    repeat (split; eauto).
    simpl; eauto.
    simpl; eauto.

  -
    simpl in H1.
    simpljoin1.
    eapply H0 in H1; eauto.

  -
    eapply H0 in H2.
    eapply IHwf_seq in H2; eauto.
    simpljoin1.
    eapply Seq_conseq_rule in H2; eauto.
Qed.

Lemma bne_preservation :
  forall p q S S1 S2 aexp pc npc pc1 npc1 pc2 npc2 Spec Spec' C i I,
     wf_seq Spec p I q -> LookupC C pc npc I -> S |= p ->
     wf_cdhp Spec C Spec' -> cdhp_subst Spec Spec' ->
     C pc = Some (cbne aexp) -> C npc = Some (cntrans i) ->
     P__ C (S, pc, npc) (S1, pc1, npc1) -> P__ C (S1, pc1, npc1) (S2, pc2, npc2) ->
     exists I' p',
       wf_seq Spec p' I' q /\ LookupC C pc2 npc2 I' /\ S2 |= p'.
Proof.
  intros.
  generalize dependent C.
  generalize dependent S.
  generalize dependent S1.
  generalize dependent S2.
  generalize dependent aexp.
  generalize dependent pc.
  generalize dependent pc1.
  generalize dependent pc2.
  generalize dependent npc.
  generalize dependent npc1.
  generalize dependent npc2.
  generalize dependent i.
 
  induction H; intros; elim_ins_neq.
 
  -
    inversion H12; subst.
    rewrite H10 in H20.
    inversion H20; subst.
    inversion H25; get_ins_diff_false.

    clear H23 H20 H21.
    eapply dly_reduce_asrt_stable in H17; eauto.
    lets Haexp : H17.
    eapply H in Haexp.
    simpl in Haexp.
    simpljoin1.
    rewrite H33 in H14.
    inversion H14; subst.
    clear H14 H15.
    assert (bv = $ 0).
    {
      clear - H2 H34 H17.
      eapply H2 in H17.
      sep_star_split_tac.
      simpls.
      simpljoin1.
      clear H2.
      unfolds regSt.
      simpls.
      simpljoin1.
      unfold merge in *.
      unfolds RegMap.set.
      destruct_rneq_H.
      inversion H34; eauto.
    }

    subst.
    inversion H13; subst.
    eapply dly_reduce_asrt_stable in H18; eauto.
    inversion H28; get_ins_diff_false.
    eapply ins_rule_sound in H1.
    eapply total_to_partial in H1.
    eapply H1 in H18; eauto.
    eapply H18 in H26; eauto.
    clear H18.
    assert (($ 0) =ᵢ ($ 0) = true).
    {
      eapply Int.eq_true; eauto.
    }
    eapply H6 in H14; eauto.
    unfold wf_cdhp in H9.
    unfold cdhp_subst in H3.
    eapply H3 in H0; eauto.
    eapply H9 with (L := L) in H0; eauto.
    simpljoin1.
    renames x to I'.
    exists I' p'.
    repeat (split; eauto).
    eapply Seq_frame_rule in H16; eauto.
    clear - H16 H14 H15.
    eapply Seq_conseq_rule; eauto.

    clear H20 H23 H22.
    eapply dly_reduce_asrt_stable in H17; eauto.
    assert (bv = v).
    {
      clear - H2 H34 H17.
      eapply H2 in H17.
      sep_star_split_tac.
      simpls.
      simpljoin1.
      unfolds regSt.
      simpls.
      simpljoin1.
      unfold merge in *.
      unfolds RegMap.set.
      destruct_rneq_H.
      inversion H34; eauto.
    }
    subst.
    inversion H13; subst.
    eapply dly_reduce_asrt_stable in H17; eauto.
    eapply ins_rule_sound in H1.
    eapply total_to_partial in H1.
    inversion H28; get_ins_diff_false.
    eapply H1 in H17; eauto.
    eapply H17 in H26; eauto.
    clear H17.
    exists I (p' //\\ [|v =ᵢ ($ 0) = false|]).
    repeat (split; eauto).
    clear - H24.
    assert ((pc1 +ᵢ ($ 4)) +ᵢ ($ 4) = pc1 +ᵢ ($ 8)).
    {
      rewrite Int.add_assoc.
      simpl; eauto.
    }
    rewrite H; eauto.
    clear - H35.
    simpl.
    unfold Int.eq.
    destruct (zeq (Int.unsigned v) (Int.unsigned $ 0)); eauto.
    eapply z_eq_to_int_eq in e.
    do 2 rewrite Int.repr_unsigned in e.
    subst.
    tryfalse.
    
  - 
    rewrite H5 in H9.
    inversion H9; subst.
    clear H9 H10.
    sep_star_split_tac.
    simpl in H13.
    simpljoin1.
    eapply bne_progress in H; eauto.
    simpljoin1.
    destruct_state x.
    destruct_state x0.
    eapply IHwf_seq in H1; eauto.
    destruct H1 as [ I' [p' H1] ].
    simpljoin1. 
    eapply program_step_safety_property with (s := (merge m m0, (merge r0 r1, f0), d0)) (r := r)
      in H; eauto.
    simpljoin1.
    destruct_state x0.
    simpl in H16.
    simpljoin1.
    eapply program_step_safety_property with (s := (merge m1 m3, (merge r2 r4, f2), d2)) (r := r)
      in H13; eauto.
    simpljoin1.
    destruct_state x0.
    simpl in H19.
    simpljoin1.
    eapply program_step_deterministic in H7; eauto.
    simpljoin1.
    eapply program_step_deterministic in H8; eauto.
    simpljoin1.
    exists I' (p' ** r).
    repeat (split; eauto).
    eapply Seq_frame_rule; eauto.
    clear - H19 H21 H20 H15.
    simpl.
    do 2 eexists.
    repeat (split; eauto).
    simpl; eauto.
    simpl; eauto.

  -
    simpl in H1.
    simpljoin1.
    eapply H0 in H1; eauto.

  -
    eapply H0 in H2.
    eapply IHwf_seq in H2; eauto.
    simpljoin1.
    eapply Seq_conseq_rule in H2; eauto.
Qed.

Lemma retl_preservation :
  forall p q Spec S S1 S2 pc npc pc1 npc1 pc2 npc2 C I,
    wf_seq Spec p I q -> LookupC C pc npc I -> S |= p -> C pc = Some cretl ->
    P__ C (S, pc, npc) (S1, pc1, npc1) -> P__ C (S1, pc1, npc1) (S2, pc2, npc2) ->
    S2 |= q.
Proof.
  intros.
  generalize dependent S.
  generalize dependent S1.
  generalize dependent S2.
  generalize dependent C.
  generalize dependent pc1.
  generalize dependent npc1.
  generalize dependent pc2.
  generalize dependent npc2.
 
  induction H; intros; elim_ins_neq.

  -
    clear H12.
    inversion H2; get_ins_diff_false.
    clear H8 H12.
    inversion H6; subst.
    inversion H16; get_ins_diff_false.
    clear H11. 
    eapply dly_reduce_asrt_stable in H10; eauto.
    inversion H4; subst.
    inversion H21; get_ins_diff_false.
    eapply dly_reduce_asrt_stable in H11; eauto.
    eapply ins_rule_sound in H.
    eapply total_to_partial in H.
    eapply H in H11; eauto.

  -
    sep_star_split_tac.
    simpl in H11.
    simpljoin1.
    eapply retl_progress in H; eauto.
    simpljoin1.
    destruct_state x.
    destruct_state x0.
    eapply IHwf_seq in H3; eauto.
    eapply program_step_safety_property with (s := (merge m m0, (merge r0 r1, f0), d0))
      (r := r) in H; eauto.
    simpljoin1.
    destruct_state x0.
    simpls.
    simpljoin1.
    eapply program_step_safety_property with (s := (merge m1 m3, (merge r2 r4, f2), d2))
       (r := r) in H9; eauto.
    simpljoin1.
    destruct_state x0.
    simpl in H14.
    simpljoin1.
    eapply program_step_deterministic in H5; eauto.
    simpljoin1.
    eapply program_step_deterministic in H4; eauto.
    simpljoin1.
    exists (m2, (r3, f), d) (m4, (r5, f), d).
    simpl; eauto. 
    repeat (split; eauto).
    simpl; eauto.
    simpl; eauto.

  -
    simpls.
    simpljoin1; eauto.

  -
    eapply H0 in H5.
    eauto.
Qed.

Lemma call_preservation :
  forall p q Spec Spec' f S S1 S2 pc pc1 pc2 npc npc1 npc2 C I,
    wf_seq Spec p I q -> LookupC C pc npc I -> S |= p ->
    wf_cdhp Spec C Spec' -> cdhp_subst Spec Spec' ->
    C pc = Some (ccall f) ->
    P__ C (S, pc, npc) (S1, pc1, npc1) -> P__ C (S1, pc1, npc1) (S2, pc2, npc2) ->
    exists I1 I2 p1 p2,
      wf_seq Spec p1 I1 p2 /\ LookupC C pc2 npc2 I1 /\ S2 |= p1 /\ p2 ==> Or r15 ==ₑ pc /\ 
      wf_seq Spec p2 I2 q /\ LookupC C (pc +ᵢ ($ 8)) (pc +ᵢ ($ 12)) I2.
Proof.
  intros.
  generalize dependent S.
  generalize dependent S1.
  generalize dependent S2.
  generalize dependent C.
  generalize dependent pc1.
  generalize dependent npc1.
  generalize dependent pc2.
  generalize dependent npc2.
  generalize dependent f.
 
  induction H; intros; elim_ins_neq.
 
  -
    clear H22.
    inversion H14; subst.
    eapply dly_reduce_asrt_stable in H18; eauto.
    eapply H0 in H18.
    inversion H23; get_ins_diff_false.
    clear H20. 
    assert ((M', (set_R R' r15 f1, F'), D'') |= r15 |=> f1 ** p1).
    {
      clear - H18.
      sep_star_split_tac.
      simpl in H3.
      simpljoin1.
      simpl.
      exists (m, (set_R r r15 f1, f0), d0) (m0, (r0, f0), d0).
      simpls.
      unfolds regSt.
      simpls.
      simpljoin1.
      repeat (split; eauto).
      eapply disjoint_setR_still1; eauto.
      rewrite indom_setR_merge_eq1; eauto.
      eapply regset_l_l_indom; eauto.
      rewrite indom_setR_eq_RegMap_set; eauto.
      rewrite regset_twice; eauto.
      eapply regset_l_l_indom; eauto.
    } 
    inversion H12; subst.
    eapply dly_reduce_asrt_stable in H20; eauto.
    eapply ins_rule_sound in H1.
    eapply total_to_partial in H1; eauto.
    inversion H31; get_ins_diff_false.
    eapply H1 in H20; eauto.
    eapply H20 in H29; eauto.
    clear H20.
    unfold cdhp_subst in H3.
    unfold wf_cdhp in H10. 
    eapply H3 in H.
    eapply H10 with (L := L) in H.
    simpljoin1.
    rename x into I'.
    eapply Seq_frame_rule with (r := r) in H16; eauto.
    exists I' I (fp L ** r) (fq L ** r).
    repeat (split; eauto).
    clear - H6.
    intros.
    sep_star_split_tac.
    simpl in H3.
    simpljoin1.
    eapply H6 in H; eauto.
    clear - H.
    simpls.
    unfold merge.
    rewrite H; eauto.
    eapply Seq_conseq_rule; eauto.
    clear - H26.
    do 2 rewrite Int.add_assoc in H26.
    simpls; eauto.

  -
    sep_star_split_tac.
    simpls.
    simpljoin1.
    eapply call_progress in H; eauto.
    simpljoin1.
    destruct_state x.
    destruct_state x0.
    eapply IHwf_seq in H5; eauto.
    simpljoin1.   
    eapply program_step_safety_property with (s := (merge m m0, (merge r0 r1, f1), d0)) (r := r)
      in H; eauto. 
    simpljoin1.
    destruct_state x8.
    simpls.
    simpljoin1.
    eapply program_step_safety_property with (s := (merge m1 m3, (merge r2 r4, f3), d2)) (r := r)
      in H12; eauto.
    simpljoin1.
    eapply program_step_deterministic in H7; eauto.
    simpljoin1.
    eapply program_step_deterministic in H6; eauto.
    destruct_state x8.
    simpls.
    simpljoin1. 
    exists x x0 (x5 ** r) (x6 ** r).
    repeat (split; eauto).
    eapply Seq_frame_rule; eauto.
    simpl.
    do 2 eexists.
    repeat (split; eauto).
    clear - H16.
    intros.
    sep_star_split_tac.
    simpls.
    simpljoin1.
    simpls.
    eapply H16 in H.
    simpls.
    unfold merge.
    rewrite H; eauto.
    eapply Seq_frame_rule; eauto.
    simpl; eauto.
    simpl; eauto.

  -
    simpls.
    simpljoin1; eauto.

  -
    eapply H0 in H7. 
    eapply IHwf_seq with (pc2 := pc2) (npc2 := npc2) in H7; eauto.
    simpljoin1.
    exists x x0 x1 x2; eauto.
    repeat (split; eauto).
    eapply Seq_conseq_rule; eauto.
Qed.
    
(*+ Lemmas for Sequence Rule +*)
    
Lemma program_step_next :
  forall C S S' pc npc pc' npc',
    P__ C (S, pc, npc) (S', pc', npc') ->
    pc' = npc.
Proof.
  intros.
  inversion H; subst.
  inversion H8; subst; eauto.
Qed.

Lemma insSeq_rule_sound :
  forall cls Spec Spec' p q I pc npc S C,
    wf_seq Spec p I q -> LookupC C pc npc I ->
    wf_cdhp Spec C Spec' -> cdhp_subst Spec Spec' -> S |= p ->
    safety_step C S pc npc q cls 0.
Proof.
  intro cls.
  induction cls; intros.
  -
    eapply safety_step_ret1; intros.
    eapply retl_preservation in H; eauto.
  -
    
  

>>>>>>>>>>>>>>>>>>>>>
    
Lemma insSeq_rule_sound :
  forall Spec Spec' p q I pc npc S C,
    wf_seq Spec p I q -> LookupC C pc npc I ->
    wf_cdhp Spec C Spec' -> cdhp_subst Spec Spec' -> S |= p ->
    safety C S pc npc q 0.
Proof.
  cofix.
  intros.
  eapply safety_cons; intros.
 
  - (** C pc = i *)
    eapply seq_preservation in H; eauto.
    simpljoin1.
    renames x to p', x0 to I'.
    eauto.

  - (** C pc = jumpl *) 
    lets Hnpc : H0.
    eapply pc_jmpl_npc_i_or_jmp in Hnpc; eauto.
    lets Ht : H5.
    eapply program_step_next in H5.
    subst.
    eapply safety_cons; intros.
  
    eapply jmpl_preservation1 in H4; eauto.
    simpljoin1. 
    renames x0 to fp, x1 to fq, x2 to L, x to I', x3 to r.
    eapply Seq_conseq_rule with (p := fp L ** r) (q := q) in H4; eauto.
 
    eapply jmpl_preservation2 with (npc := npc) in H4; eauto.
    simpljoin1.
    renames x0 to fp, x1 to fq, x2 to L, x to I', x3 to r. 
    eapply Seq_conseq_rule with (p := fp L ** r) (q := q) in H4; eauto.

    Local Ltac jmp_continue_fail H :=
      destruct H as [ [?i H] | [?aexp [?r H] ] ];
      [get_ins_diff_false | get_ins_diff_false].

    jmp_continue_fail Hnpc.
    jmp_continue_fail Hnpc.
    jmp_continue_fail Hnpc.
    jmp_continue_fail Hnpc.
 
  - (** C pc = be aexp *)
    lets Hnpc : H4.
    eapply pc_be_npc_i in Hnpc; eauto.
    destruct Hnpc as [i Hnpc].
    lets Ht : H5.
    eapply program_step_next in H5.
    subst.
    eapply safety_cons;
      try solve [intros; get_ins_diff_false].
    intros.
    rewrite Hnpc in H5.
    inversion H5; subst.
    clear H5.
    eapply be_preservation in H; eauto.
    simpljoin1.
    renames x0 to p', x to I'.
    eauto.

  - (** C pc = bne aexp *)
    lets Hnpc : H4.
    eapply pc_bne_npc_i in Hnpc; eauto.
    destruct Hnpc as [i Hnpc].
    lets Ht : H5.
    eapply program_step_next in H5.
    subst.
    eapply safety_cons;
      try solve [intros; get_ins_diff_false].
    intros.
    rewrite Hnpc in H5.
    inversion H5; subst.
    clear H5.
    eapply bne_preservation in H; eauto.
    simpljoin1.
    renames x0 to p', x to I'.
    eauto.

  - (** C pc = call f *)  
    eapply call_preservation in H; eauto.
    simpljoin1. 
    renames x1 to p1, x2 to p2, x to Ic, x0 to I'.
    admit.
    
  - (** retl *)
    left.
    split; eauto.
    eapply retl_preservation; eauto.
    
    
    >>>>>>>>>>>>>>>>>
    
  
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

  