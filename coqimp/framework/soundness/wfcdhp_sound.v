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
  forall p q S S1 S2 aexp rd pc pc1 pc2 npc npc1 npc2 Spec C i I,
    wf_seq Spec p I q -> LookupC C pc npc I -> S |= p ->
    C pc = Some (cjumpl aexp rd) -> C npc = Some (cntrans i) ->
    P__ C (S, pc, npc) (S1, pc1, npc1) -> P__ C (S1, pc1, npc1) (S2, pc2, npc2) ->
    exists I' fp fq L,
      wf_seq Spec (fp L) I' (fq L) /\ LookupC C pc2 npc2 I' /\
      Spec (pc2, npc2) = Some (fp, fq) /\ S2 |= (fp L) /\ fq L ==> q.
Proof.
Admitted.

Lemma jmpl_preservation2 :
  forall p q S S1 S2 aexp1 aexp2 r1 r2 pc pc1 pc2 npc npc1 npc2 Spec C I,
    wf_seq Spec p I q -> LookupC C pc npc I -> S |= p ->
    C pc = Some (cjumpl aexp1 r1) -> C npc = Some (cjumpl aexp2 r2) ->
    P__ C (S, pc, npc) (S1, pc1, npc1) -> P__ C (S1, pc1, npc1) (S2, pc2, npc2) ->
    exists I' fp fq L,
      wf_seq Spec (fp L) I' (fq L) /\ LookupC C pc2 npc2 I' /\
      Spec (pc2, npc2) = Some (fp, fq) /\ S2 |= (fp L) /\ fq L ==> q.
Proof.
Admitted.

Lemma program_step_next :
  forall C S S' pc npc pc' npc',
    P__ C (S, pc, npc) (S', pc', npc') ->
    pc' = npc.
Proof.
Admitted.
  
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
    renames x0 to fp, x1 to fq, x2 to L, x to I'.
    eapply Seq_conseq_rule with (p := fp L) (q := q) in H4; eauto.

    eapply jmpl_preservation2 in H4; eauto.
    simpljoin1.
    renames x0 to fp, x1 to fq, x2 to L, x to I'.
    eapply Seq_conseq_rule with (p := fp L) (q := q) in H4; eauto.
    
    
    >>>>>>>>>>>>>>>>>
    
  
  
  cofix.
  intros.
  inversion H; subst.
 
  - (** Seq *)
    inversion H0; subst.
    clear H.
    eapply safety_cons;
      try solve [intros; get_ins_diff_false].
    intros.
    rewrite H11 in H.
    inversion H; subst.
    clear H.
    inversion H6; subst.
    eapply ins_rule_sound in H4.
    eapply total_to_partial in H4; eauto.
    inversion H16; get_ins_diff_false.
    eapply dly_reduce_asrt_stable in H3; eauto.

  - (** Call *)
    eapply call_test.

  - (** retl *)
    clear H.
    inversion H0; subst.
    eapply safety_cons;
      try solve [intros; get_ins_diff_false].
    intros.
    left.
    inversion H7; subst.
    clear H11.
    inversion H19; get_ins_diff_false.
    eapply dly_reduce_asrt_stable in H3; eauto.
    clear H14.
    inversion H8; subst.
    eapply dly_reduce_asrt_stable in H3; eauto.
    inversion H23; get_ins_diff_false.
    eapply ins_rule_sound in H4.
    eapply total_to_partial in H4.
    eapply H4 in H3; eauto.

  - (** J1 *)
    
    clear H.
    inversion H0; subst.
    eapply safety_cons;
      try solve [intros; get_ins_diff_false].
    intros.
    inversion H11; subst.
    eapply dly_reduce_asrt_stable in H3; eauto.
    inversion H22; get_ins_diff_false.
    rewrite H15 in H.
    inversion H; subst.
    clear H15 H21.
    lets Hp : H3.
    eapply H4 in Hp.
    simpl in Hp.
    simpljoin1.
    rewrite H30 in H12.
    inversion H12; subst.
    clear H12.
    eapply safety_cons;
      try solve [intros; get_ins_diff_false].
    intros.
    inversion H12; subst.
    inversion H28; get_ins_diff_false.
    clear H20 H12 H28.
    lets Ht : H3.
    eapply H6 in Ht.
    eapply sep_star_split in Ht.
    destruct Ht as [ s1 [s2 [Hs1 [Hs2 Hunion] ] ] ].
    destruct_state s1.
    destruct_state s2.
    simpl in Hunion.
    simpljoin1.
    rename pc'0 into f.

    assert (Hset_rd : (m, (set_R r0 rd0 f1, f0), d0) |= rd0 |=> f1).
    {
      clear - Hs1.
      simpls.
      unfolds regSt.
      simpls.
      simpljoin1.
      repeat (split; eauto).
      rewrite indom_setR_eq_RegMap_set; eauto.
      rewrite regset_twice; eauto.
      eapply regset_l_l_indom; eauto.
    }

    assert (Hset_rd_asrt :
              (merge m m0, (merge (set_R r0 rd0 f1) r1, f0), d0) |= rd0 |=> f1 ** p1).
    {
      clear - Hset_rd H12 H14 Hs1 Hs2.
      simpls.
      exists (m, (set_R r0 rd0 f1, f0), d0) (m0, (r1, f0), d0).
      simpl.
      repeat (split; eauto).
      eapply disjoint_setR_still1; eauto.
    }
    rewrite <- indom_setR_merge_eq1 in Hset_rd_asrt; eauto.
    eapply ins_rule_sound in H7.
    eapply total_to_partial in H7.
    eapply dly_reduce_asrt_stable in Hset_rd_asrt; eauto.
    rewrite H19 in H.
    inversion H; subst.
    eapply H7 in Hset_rd_asrt; eauto.
    eapply Hset_rd_asrt in H26; eauto.  
    clear - insSeq_rule_sound H1 H2 H5 H26 H8 H9 H10.
    lets Hwfcdhp : H1.
    lets Hcdhpsubst : H2.
    unfold wf_cdhp in H1.
    unfold cdhp_subst in H2.
    eapply H2 in H5; eauto.
    eapply H1 with (L := L) in H5.
    simpljoin1.
    rename x into I.
    eapply H8 in H26.
    eapply Seq_frame_rule with (r := r) in H0; eauto.
    clear H1 H2.
    eapply insSeq_rule_sound in H0; eauto.
    eapply safety_post_weak in H0; eauto.
    clear - Hset_rd.
    simpls.
    unfolds regSt.
    simpls.
    simpljoin1.
    unfolds set_R.
    unfold is_indom in *.
    destruct (r0 rd0) eqn:Heqe; tryfalse.
    unfold indom; eauto.
    subst.
    unfolds RegMap.set.
    destruct_rneq_H.

  - (** J2 *)
    eapply call_test.
    
    (*
    inversion H0; subst.
    eapply safety_cons;
      try solve [intros; get_ins_diff_false].
    intros.
    rewrite H17 in H12.
    inversion H12; subst.
    inversion H13; subst.
    lets Hp : H3.
    eapply dly_reduce_asrt_stable in Hp; eauto.
    clear H18 H13.
    inversion H24; get_ins_diff_false.
    lets Hf1 : Hp.
    eapply H4 in Hf1; eauto.
    simpl in Hf1.
    simpljoin1.
    rewrite H30 in H13.
    inversion H13; subst.
    clear H13.
    lets Hrd : Hp.
    eapply H5 in Hrd; eauto.
    assert ((M', (set_R R' rd0 f1, F'), D'') |= rd0 |=> f1 ** p1).
    {
      clear - Hrd.
      sep_star_split_tac.
      simpl in H3.
      simpljoin1.
      simpl.
      exists (m, (set_R r rd0 f1, f0), d0) (m0, (r0, f0), d0).
      simpls.
      repeat (split; eauto).
      eapply disjoint_setR_still1; eauto.
      rewrite indom_setR_merge_eq1; eauto.
      clear - H1.
      unfolds regSt.
      simpls.
      simpljoin1.
      eapply regset_l_l_indom; eauto.
      simpls.
      rewrite indom_setR_eq_RegMap_set; eauto.
      unfolds regSt.
      simpls.
      simpljoin1.
      rewrite regset_twice; eauto.
      unfolds regSt.
      simpls.
      simpljoin1.
      eapply regset_l_l_indom; eauto.
      simpl; eauto.
      unfolds regSt.
      simpls.
      simpljoin1; eauto.
    }
    
    eapply safety_cons;
      try solve [intros; get_ins_diff_false].
    intros.
    rewrite H22 in H13.
    inversion H13; subst.
    inversion H15; subst.
    clear H15.
    eapply dly_reduce_asrt_stable in H12; eauto.
    lets Hp' : H12.
    eapply H7 in H12.
    inversion H33; get_ins_diff_false.
    eapply H6 in Hp'.
    simpl in Hp'.
    simpljoin1. 
    clear H20.
    rewrite H15 in H37.
    inversion H37; subst; eauto.

    assert ((M'0, (set_R R'0 rd1 pc', F'0), D''0) |= rd1 |=> pc' ** p2).
    {
      clear - H12.
      sep_star_split_tac.
      simpl in H3.
      simpljoin1.
      simpls.
      unfolds regSt.
      simpls.
      simpljoin1.
      exists (empM, (set_R (RegMap.set rd1 (Some v2) empR) rd1 pc', f0), d0)
        (m0, (r0, f0), d0).
      simpl.
      repeat (split; eauto).
      eapply disjoint_setR_still1; eauto. 
      rewrite indom_setR_merge_eq1; eauto.
      eapply regset_l_l_indom; eauto.
      rewrite indom_setR_eq_RegMap_set; eauto.
      rewrite regset_twice; eauto.
      eapply regset_l_l_indom; eauto.
    }

    eapply H9 in H13.   
    clear - insSeq_rule_sound H1 H2 H8 H10 H13 H11.
    lets Hwfcdhp : H1.
    unfold wf_cdhp in H1.
    lets Hcdhpsubset : H2.
    unfold cdhp_subst in H2.
    eapply H2 in H8.
    eapply H1 with (L := L) in H8; eauto.
    simpljoin1.
    rename x into I. 
    eapply Seq_frame_rule with (r := r) in H0; eauto.
    eapply insSeq_rule_sound in H0; eauto.
    eapply safety_post_weak in H0; eauto. *)

  - (** be *)
    
    inversion H0; subst.
    eapply safety_cons;
      try solve [intros; get_ins_diff_false].
    clear H H0.
    intros.
    rewrite H17 in H.
    inversion H; subst.
    inversion H0; subst.
    eapply dly_reduce_asrt_stable in H14; eauto.
    lets Hp1 : H14.
    eapply H4 in Hp1; eauto.  
    inversion H22; get_ins_diff_false.

    eapply call_test.
    (*
    simpl in Hp1.
    simpljoin1.  
    rewrite H11 in H30.
    inversion H30; subst.
    clear H30 H17. 
    
    assert (v = bv).
    {
      clear - H7 H14 H31.
      eapply H7 in H14.
      sep_star_split_tac.
      simpl in H3.
      simpljoin1.
      clear - H1 H31.
      simpl in H1.
      unfolds regSt.
      simpls.
      simpljoin1.
      unfolds RegMap.set.
      unfold merge in *.
      destruct_rneq_H.
      inversion H31; subst; eauto.
    }

    subst v.
    eapply safety_cons;
      try solve [intros; get_ins_diff_false].
    intros.
    rewrite H20 in H.
    inversion H; subst.
    clear H.
    inversion H13; subst.
    inversion H28; get_ins_diff_false.
    eapply dly_reduce_asrt_stable in H17; eauto.
    eapply ins_rule_sound in H6.
    eapply total_to_partial in H6.
    eapply H6 in H17; eauto.
    eapply H17 in H26; eauto.
    clear H17 H18.   
    clear - insSeq_rule_sound H5 H9 H10 H32 H26 H1 H2 H21.
    assert (Hbv_false : bv =ᵢ ($ 0) = false).
    {
      clear - H32.
      unfold Int.eq.
      destruct (zeq (Int.unsigned bv) (Int.unsigned $ 0)); eauto.
      {
        eapply z_eq_to_int_eq in e.
        rewrite Int.repr_unsigned in e.
        rewrite Int.repr_unsigned in e.
        subst.
        tryfalse.
      }
    }
    eapply H10 in Hbv_false.
    simpljoin1.
    lets Hwfcdhp : H1.
    lets Hcdhpsubst : H2.
    unfold wf_cdhp in H1.
    unfold cdhp_subst in H2.
    eapply H2 in H5.
    eapply H1 with (L := L) in H5.
    simpljoin1.
    rename x into I.
    eapply H in H26.
    eapply Seq_frame_rule with (r := r) in H4; eauto.
    eapply insSeq_rule_sound in H4; eauto.
    eapply safety_post_weak; eauto.
*)

    clear H17.
    eapply safety_cons;
      try solve [intros; get_ins_diff_false].
    intros.
    rewrite H20 in H11. 
    inversion H11; subst.
    clear H11.
    inversion H12; subst.
    lets Hp' : H14.
    eapply dly_reduce_asrt_stable in Hp'; eauto.
    inversion H28; get_ins_diff_false.
    lets Hp1' : H14.
    simpl in Hp1.
    simpljoin1.
    rewrite H11 in H30.
    inversion H30; subst.
    eapply ins_rule_sound in H6.
    eapply total_to_partial in H6.
    eapply H6 in Hp'; eauto.
    eapply Hp' in H26; eauto. 
    clear Hp'.
    assert (bv =ᵢ ($ 0) = true).
    {
      eapply H7 in H14.
      clear - H14 H31.
      sep_star_split_tac.
      simpl in H1.
      simpl in H3.
      simpljoin1.
      unfolds regSt.
      simpls.
      simpljoin1.
      clear - H31.
      unfolds RegMap.set.
      unfold merge in *.
      destruct_rneq_H.
      inversion H31.
      unfold Int.eq.
      assert (Int.unsigned Int.zero = 0%Z).
      eapply Int.unsigned_zero; eauto.
      unfold Int.zero in H0.
      rewrite H0; eauto.
    }
    clear - insSeq_rule_sound H1 H2 H8 H21 H26 H.
    eapply insSeq_rule_sound in H8; eauto.
    assert (pc' +ᵢ ($ 8) = (pc' +ᵢ ($ 4)) +ᵢ ($ 4)).
    {
      rewrite Int.add_assoc.
      assert ($ 8 = ($ 4) +ᵢ ($ 4)).
      eauto.
      rewrite <- H0.
      eauto.
    }
    rewrite <- H0.
    eauto.
    simpl; eauto.

  - (** Bne *)
    eapply call_test.
    
  (*
    clear H.
    inversion H0; subst.
    eapply safety_cons;
      try solve [intros; get_ins_diff_false].
    intros.
    inversion H11; subst.
    clear H11.
    eapply dly_reduce_asrt_stable in H15; eauto.
    lets Hp1 : H15.
    eapply H4 in H15.
    simpl in H15. 
    simpljoin1.
    inversion H23; get_ins_diff_false.
    rewrite H16 in H.
    inversion H; subst.
    rewrite H11 in H31.
    inversion H31; subst.
    clear H31 H21 H H16.
    assert (bv = $ 0).
    {
      clear - Hp1 H32 H7.
      eapply H7 in Hp1.
      sep_star_split_tac.
      simpl in H3.
      simpljoin1.
      simpl in H1.
      unfolds regSt.
      simpls.
      simpljoin1.
      unfold merge in H32.
      unfolds RegMap.set.
      destruct_rneq_H.
      inversion H32; eauto.
    }
    subst.
    eapply safety_cons;
      try solve [intros; get_ins_diff_false].
    intros.
    rewrite H19 in H.
    inversion H; subst.
    clear H.
    inversion H13; subst.
    eapply dly_reduce_asrt_stable in H16; eauto.
    eapply ins_rule_sound in H6.
    eapply total_to_partial in H6; eauto.
    inversion H27; get_ins_diff_false.
    eapply H6 in H16; eauto.
    eapply H16 in H25; eauto.
    clear H16. 
    clear - insSeq_rule_sound H1 H2 H5 H25 H10 H9.
    lets Hwfcdhp : H1.
    lets Hcdhpsubset : H2.
    unfold wf_cdhp in H1.
    unfold cdhp_subst in H2.
    eapply H2 in H5.
    eapply H1 with (L := L) in H5; eauto.
    assert (($ 0) =ᵢ ($ 0) = true).
    {
      rewrite Int.eq_true; eauto.
    } 
    eapply H10 in H.
    simpljoin1.
    eapply H in H25; eauto.
    eapply Seq_frame_rule with (r := r) in H4; eauto.
    eapply insSeq_rule_sound in H4; eauto.
    eapply safety_post_weak; eauto.

    rewrite H16 in H.
    inversion H; subst.
    clear H16.
    eapply safety_cons;
      try solve [intros; get_ins_diff_false].
    intros.
    inversion H14; subst.
    eapply dly_reduce_asrt_stable in H18; eauto.
    eapply ins_rule_sound in H6.
    eapply total_to_partial in H6.
    inversion H30; get_ins_diff_false.
    rewrite H19 in H13.
    inversion H13; subst.
    clear H19 H21 H13.
    eapply H6 in H18; eauto.
    eapply H18 in H28; eauto.
    clear H18.
    assert (bv = v).
    {
      clear - H7 Hp1 H32.
      eapply H7 in Hp1; eauto.
      sep_star_split_tac.
      simpl in H3.
      simpljoin1.
      simpl in H1.
      unfolds regSt.
      simpls.
      simpljoin1.
      unfold merge in H32.
      unfolds RegMap.set.
      destruct_rneq_H.
      inversion H32; eauto.
    }
    subst.
    clear - insSeq_rule_sound H1 H2 H5 H8 H28 H20 H33.
    eapply insSeq_rule_sound in H8; eauto.
    assert (pc' +ᵢ ($ 8) = (pc' +ᵢ ($ 4)) +ᵢ ($ 4)).
    {
      rewrite Int.add_assoc; eauto.
    }
    rewrite <- H.
    eauto.
    simpl.
    split; eauto.
    clear - H33.
    unfold Int.eq.
    destruct (zeq (Int.unsigned v) (Int.unsigned $ 0)) eqn:Heqe; eauto.
    clear Heqe.
    eapply z_eq_to_int_eq in e.
    do 2 rewrite Int.repr_unsigned in e.
    subst.
    tryfalse.
*)

  - (** frame *)
    eapply call_test.
 
  - (** ex_intro *)
    eapply call_test.
    (*
    clear H.
    simpl in H3.
    simpljoin1.
    specialize (H4 x).
    eapply insSeq_rule_sound in H4; eauto.*)
Qed.


    
  - (** Seq *)
    inversion H4; subst.
    eapply safety_cons;
      try solve [intros; get_ins_diff_false].
    intros.

    inversion H6; subst.
    inversion H17; get_ins_diff_false.
    rewrite H10 in H5; inversion H5; subst.
    eapply ins_rule_sound in H.
    eapply total_to_partial in H.
    eapply dly_reduce_asrt_stable in H3; eauto.

  - (** Call *)
    admit.

  - (** retl *)
    inversion H5; subst.
    eapply safety_cons;
      try solve [intros; get_ins_diff_false].
    intros.

    left.
    inversion H7; subst.
    inversion H19; get_ins_diff_false.
    eapply dly_reduce_asrt_stable in H4; eauto.
    clear H11 H14 H15.
    inversion H8; subst.
    inversion H22; get_ins_diff_false.
    eapply ins_rule_sound in H.
    eapply total_to_partial in H; eauto.
    eapply dly_reduce_asrt_stable in H4; eauto.

  - (** jumpl *)
    inversion H9; subst.
    
    
    >>>>>>>>>>>>>>>>
    
  
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

  