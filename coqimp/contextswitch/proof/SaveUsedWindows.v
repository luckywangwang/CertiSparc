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

Require Import integer_lemma.

Require Import sep_lemma.
Require Import reg_lemma.
Require Import derived_rule.

Require Import tm_dly_lemma.

Require Import code.
Require Import ctxswitch_spec.

Require Import lemma1.

Open Scope nat.
Open Scope code_scope.
Open Scope mem_scope.

(*+ Lemmas +*)
Ltac solve_element_vi vi :=
  match goal with
  | H : vi = _ \/ _ |- _ =>
    destruct H as [?a | H]; [subst; tryfalse; eauto | solve_element_vi vi]
  | H : vi = _ |- _ =>
    subst; tryfalse; eauto
  | _ => idtac
  end.

Ltac solve_element_id id vi :=
  match goal with
  | H : id = _ \/ _ |- _ =>
    destruct H as [?a | H];
    [subst; solve_element_vi vi | solve_element_id id vi]
  | H : id = _ |- _ =>
    subst; solve_element_vi vi
  | _ => idtac
  end.

Lemma post_cons_neq_still :
  forall id vi,
    $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 -> $ 0 <=ᵤᵢ vi <=ᵤᵢ $ 7 ->
    id <> post_cwp vi ->
    post_cwp id <> post_cwp (post_cwp vi).
Proof.
  intros.
  intro.
  eapply H1.
  unfolds post_cwp.
  eapply in_range_0_7_num in H.
  eapply in_range_0_7_num in H0.
  unfolds N.
  solve_element_id id vi.
Qed.

Lemma post_cons_neq_still_rev :
  forall id vi,
    post_cwp id <> post_cwp (post_cwp vi) ->
    id <> post_cwp vi.
Proof.
  intros.
  intro.
  eapply H.
  subst; eauto.
Qed.

Lemma post_1_neq' :
  forall id,
    $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 ->
    id <> post_cwp id.
Proof.
  intros.
  intro.
  symmetry in H0.
  eapply post_1_neq in H0; eauto.
Qed.

Lemma in_range228 : 
  ($ (-4096)) <=ᵢ ($ 228) && ($ 228) <=ᵢ ($ 4095) = true.
Proof.
  eauto.
Qed.

(*+ Lemma for stack frame relation +*)

Lemma stack_frame_match_fm_save :
  forall fm F oid id cl clfp1 clfp2,
    $ 0 <=ᵤᵢ oid <=ᵤᵢ $ 7 -> $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 ->
    stack_frame_match oid clfp1 (F ++ fm :: nil) id -> length F = 13 ->
    stack_frame_save (F ++ fm :: nil) (cl, clfp1 ++ clfp2)
                     (cl, clfp1 ++ clfp2) oid (post_cwp id).
Proof.
  intros.
  unfold stack_frame_save.
  split; eauto.
  do 14 (try destruct F; simpl in H2; tryfalse).
  simpl in H1.
  
  inversion H1; subst.
  {
    simpl.
    eapply frame_save_end; eauto.
  }

  inversion H10; subst.
  {
    simpl. 
    eapply frame_save_cons; eauto.
    eapply post_cons_neq_still; eauto.
    eapply frame_save_end; eauto.
  }

  Ltac solve_post_inrange :=
    match goal with
    | |- $ 0 <=ᵤᵢ (post_cwp _) <=ᵤᵢ $ 7 =>
      eapply in_range_0_7_post_cwp_still; solve_post_inrange
    | _ => eauto
    end.

  Ltac solve_post_neq :=
    match goal with
    | |- post_cwp _ <> post_cwp (post_cwp _) =>
      eapply post_cons_neq_still;
      [solve_post_inrange | solve_post_inrange | solve_post_neq]
    | |- ?id <> post_cwp ?id =>
      eapply post_1_neq'; solve_post_inrange
    | _ => eauto
    end.
  
  inversion H12; subst.
  {
    simpl. 
    do 2 (eapply frame_save_cons; [solve_post_neq | idtac]).
    eapply frame_save_end; eauto.
  }
  
  inversion H14; subst.
  {
    simpl.
    do 2 (eapply frame_save_cons; [solve_post_neq | idtac]).
    eapply post_cons_neq_still_rev; eauto.
    eapply frame_save_cons; [solve_post_neq | idtac].
    eapply frame_save_end; eauto.
  }
  
  inversion H16; subst.
  {
    simpl.
    do 3 (eapply frame_save_cons; [solve_post_neq | idtac];
          try eapply post_cons_neq_still_rev; eauto).
    eapply post_cons_neq_still_rev; eauto.
    eapply frame_save_cons; [solve_post_neq | idtac].
    eapply frame_save_end; eauto.
  }

  inversion H18; subst.
  {
    simpl.
    do 4 (eapply frame_save_cons; [solve_post_neq | idtac];
          do 2 (try eapply post_cons_neq_still_rev; eauto)).
    eapply post_cons_neq_still_rev; eauto.
    eapply frame_save_cons; [solve_post_neq | idtac];
      do 2 (try eapply post_cons_neq_still_rev; eauto).
    eapply frame_save_end; eauto.
  }

  inversion H20; subst.
  {
    simpl.
    do 6 (try eapply frame_save_cons; [solve_post_neq | idtac];
          repeat (eapply post_cons_neq_still_rev; eauto)).
    eapply frame_save_end; eauto.
  }

  inversion H22; subst.
  {
    simpl.
    do 7 (try eapply frame_save_cons; [solve_post_neq | idtac];
          repeat (eapply post_cons_neq_still_rev; eauto)).
    eapply frame_save_end; eauto.
  }
Qed.

Lemma stk_fm_match_stk_len_lt_13 :
  forall oid clfp F id,
    $ 0 <=ᵤᵢ oid <=ᵤᵢ $ 7 -> $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 ->
    stack_frame_match oid clfp F id -> length F = 14 ->
    length clfp < 8.
Proof.
  intros.
  do 15 (destruct F; simpl in H2; tryfalse).
  
  inversion H1; subst; simpl; try omega.
  inversion H10; subst; simpl; try omega.
  inversion H12; subst; simpl; try omega.
  inversion H14; subst; simpl; try omega.
  inversion H16; subst; simpl; try omega.
  inversion H18; subst; simpl; try omega.
  inversion H20; subst; simpl; try omega.
  inversion H22; subst; simpl; try omega.
Qed.

(*+ Lemmas for Space +*)
Lemma stack'_split :
  forall lfp1 lfp2 l s p,
    length lfp1 < 100 ->
    s |= stack' l (lfp1 ++ lfp2) ** p ->
    s |= stack' l lfp1 ** stack' (l -ᵢ ($ (64 * Z.of_nat (length lfp1)))) lfp2 ** p.
Proof.
  intro lfp1.
  induction lfp1; intros.
  -
    simpl stack' in H0.
    simpl stack'.
    eapply astar_emp_intro_l; eauto.
    rewrite Int.sub_zero_l; eauto.
  -
    destruct a.
    simpl stack' in H0.
    simpl stack' at 1.
    eapply astar_assoc_elim in H0.
    eapply astar_assoc_intro.
    sep_cancel1 1 1.
    eapply IHlfp1 in H1; eauto.
    sep_cancel1 1 1.
    simpl length.
    rewrite Nat2Z.inj_succ.
    unfold Z.succ.
    do 2 rewrite Int.sub_add_opp in H0.
    rewrite Int.sub_add_opp.
    rewrite Int.add_assoc in H0.
    rewrite <- Int.neg_add_distr in H0.
    remember (length lfp1) as lenlfp1.
    assert (($ 64) +ᵢ ($ (64 * Z.of_nat lenlfp1)) = $ (64 * (Z.of_nat lenlfp1 + 1))).
    {
      rewrite Int.add_unsigned.
      assert (Int.unsigned $ 64 = 64%Z).
      eauto.
      rewrite H1; eauto.
      rewrite Int.unsigned_repr; eauto.
      assert ((64 * (Z.of_nat lenlfp1 + 1) = 64 + 64 * Z.of_nat lenlfp1)%Z).
      omega.
      rewrite H2.
      eauto.
      subst lenlfp1.
      clear - H.
      simpl in H.
      unfold Int.max_unsigned, Int.modulus.
      unfold two_power_nat.
      simpl shift_nat.
      omega.
    }
    rewrite H1 in H0.
    eauto.
    simpl in H.
    omega.
Qed.

Lemma stack'_cons_tail :
  forall lfp l s p fm1 fm2,
    length lfp < 100 ->
    s |= stack' l lfp ** stack_frame (l -ᵢ ($ (64 * Z.of_nat (length lfp)))) fm1 fm2 ** p ->
    s |= stack' l (lfp ++ (fm1, fm2) :: nil) ** p.
Proof.
  intro lfp.
  induction lfp; intros.
  -
    simpl stack' in *.
    simpl length in *.
    eapply astar_assoc_intro; eauto.
    assert ((64 * Z.of_nat 0 = 0)%Z).
    simpl. eauto.
    rewrite H1 in H0.
    rewrite Int.sub_zero_l in H0.
    sep_cancel1 2 1.
    eauto.
  -
    destruct a.
    simpl length in H0.
    simpl stack' in *.
    eapply astar_assoc_elim in H0.
    eapply astar_assoc_intro; eauto.
    sep_cancel1 1 1.
    eapply IHlfp; eauto.
    simpl in H; omega.
    rewrite Nat2Z.inj_succ in H1.
    unfold Z.succ in H1.
    sep_cancel1 1 1.
    rewrite Int.sub_add_opp in H0.
    do 2 rewrite Int.sub_add_opp.
    rewrite Int.add_assoc.
    rewrite <- Int.neg_add_distr.
    assert (($ 64) +ᵢ ($ (64 * Z.of_nat (length lfp))) =
            $ (64 * (Z.of_nat (length lfp) + 1))).
    {
      rewrite Int.add_unsigned; eauto.
      assert (Int.unsigned $ 64 = 64%Z).
      eauto.
      rewrite H1.
      rewrite Int.unsigned_repr; eauto.
      assert ((64 * (Z.of_nat (length lfp) + 1) = 64 + 64 * Z.of_nat (length lfp))%Z).
      omega.
      rewrite H2.
      eauto.
      unfolds Int.max_unsigned, Int.modulus, two_power_nat.
      simpl shift_nat.
      simpl in H.
      omega.
    }
    rewrite H1.
    eauto.
Qed.
  
(*+ Proof +*)
Theorem Ta0SaveUsedWindowsProof :
  forall vl,
    spec |- {{ ta0_save_usedwindows_pre vl }}
             ta0_save_usedwindows
           {{ ta0_save_usedwindows_post vl }}.
Proof.
  intros.
  unfold ta0_save_usedwindows_pre.
  unfold ta0_save_usedwindows_post.
  hoare_ex_intro_pre. 
  renames x'0 to fmg', x'2 to fmo', x'4 to fml', x'6 to fmi'.
  renames x'8 to id, x'12 to vi, x'10 to F', x'11 to vy.
  renames x'23 to vz, x'24 to vn, x'15 to ct, x'20 to nt, x'13 to ll.
  renames x'16 to cctx, x'17 to cl, x'18 to clfp1, x'19 to clfp2.
  renames x'21 to nctx, x'22 to nstk.
  renames x'7 to oid, x'1 to fmo, x'3 to fml, x'5 to fmi, x'9 to F, x'14 to i.

  eapply Pure_intro_rule.
  introv Hlgvl.
  hoare_lift_pre 15.
  eapply Pure_intro_rule.
  introv Hnctx.
  hoare_lift_pre 15.
  eapply Pure_intro_rule.
  introv Hstk_fm_match.
  hoare_lift_pre 15.
  eapply Pure_intro_rule.
  introv Hfm_restore.
  hoare_lift_pre 15.
  eapply Pure_intro_rule.
  introv Hstk_fm_constraint.
  hoare_lift_pre 15.
  eapply Pure_intro_rule.
  introv Hg4.
  destruct Hg4 as [Hg4 [Hrot [Hoid_range [Hg4_vl Hg7] ] ] ].
  hoare_lift_pre 15.
  eapply Pure_intro_rule.
  introv Hctx_win_save.
  
  unfold ta0_save_usedwindows.
 
  destruct fmg', fmo', fml', fmi'.
  
  (** sll g4 1 g5 *)
  hoare_lift_pre 2.
  eapply backward_rule.
  introv Hs.
  eapply Regs_Global_combine_GenRegs in Hs; eauto.
  eapply seq_rule; eauto.
  TimReduce_simpl.
  eapply sll_rule_reg; eauto.
  simpl; eauto.
  rewrite in_range1; eauto.
  simpl upd_genreg.
  rewrite get_range_0_4_stable; eauto.

  (** srl g4 (OS_WINDOWS - 1) g4 *)
  unfold OS_WINDOWS.
  assert (Heq7 : ($ 8) -ᵢ ($ 1) = ($ 7)).
  eauto.
  rewrite Heq7; eauto.
  eapply seq_rule; eauto.
  TimReduce_simpl.
  eapply srl_rule_reg; eauto.
  simpl; eauto.
  rewrite in_range7; eauto.
  simpl upd_genreg.
  
  simpl in Hg4.
  inversion Hg4; subst.
  rewrite get_range_0_4_stable; eauto.

  (** or g4 g5 g4 *)
  eapply seq_rule.
  TimReduce_simpl.
  eapply or_rule_reg; eauto.
  simpl; eauto.
  simpl upd_genreg.

  (** andcc g4 g7 g0 *)
  hoare_lift_pre 4.
  hoare_lift_pre 5.
  hoare_lift_pre 3.
  eapply seq_rule; eauto.
  TimReduce_simpl.
  eapply andcc_rule_reg; eauto.
  simpl; eauto.
  simpl upd_genreg.
  simpl get_genreg_val; eauto.

  (** bne Ta0_Task_Switch_NewContext; nop *)
  simpl in Hg7.
  destruct Hg7 as [Hg7 Hct_not_null].
  inversion Hg7; subst.
  eapply hoare_pure_gen' with (pu := $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 /\ $ 0 <=ᵤᵢ vi <=ᵤᵢ $ 7).
  {
    introv Hs.
    simpl_sep_liftn_in Hs 4.
    unfold FrameState in Hs.
    asrt_to_line_in Hs 3.
    simpl_sep_liftn_in Hs 4.
    eapply sep_pure_l_elim in Hs; eauto.
    simpljoin1; eauto.
  }
  eapply Pure_intro_rule.
  introv Hid_inrange.
  destruct Hid_inrange as [Hid_inrange Hvi_inrange].
  
  assert (Hiszero : iszero ((i >>ᵢ ($ 7)) |ᵢ (i <<ᵢ ($ 1))) &ᵢ (($ 1) <<ᵢ vi) =
          iszero (get_range 0 7 (i >>ᵢ ($ 7)) |ᵢ (i <<ᵢ ($ 1))) &ᵢ (($ 1) <<ᵢ vi)).
  {
    rewrite in_range_0_7_and; eauto.
  }
  rewrite Hiszero.
  rewrite g4_val_get_range_0_7_equal with (id := id); eauto.
  
  eapply Bne_rule; eauto.
  {
    eval_spec.
  }
  {
    TimReduce_simpl.
    eapply nop_rule; eauto.
  }
  {
    TimReduce_simpl.
    introv Hs.
    sep_cancel1 3 1.
    simpl; eauto.
  }

  Focus 3.
  introv Hnxt_invalid.
  unfold iszero in Hnxt_invalid.
  destruct (Int.eq_dec (($ 1) <<ᵢ (post_cwp id)) &ᵢ (($ 1) <<ᵢ vi) $ 0); tryfalse.
  clear Hnxt_invalid.
  renames n to Hnxt_invalid.
  eapply and_not_zero_eq in Hnxt_invalid; eauto.

  split.
  
    introv Hs.
    unfold ta0_task_switch_newcontext_pre.
    sep_ex_intro.
    asrt_to_line 14.
    eapply sep_pure_l_intro; eauto.
    simpl_sep_liftn 2.
    eapply GenRegs_split_Regs_Global.
    sep_cancel1 1 1.
    sep_cancel1 3 1.
    sep_cancel1 3 1.
    sep_cancel1 1 2.
    do 5 sep_cancel1 1 1.
    sep_cancel1 3 1.
    sep_cancel1 3 1.
    eapply sep_pure_l_intro; eauto.
    eapply sep_pure_l_intro; eauto.

    introv Hs.
    unfold ta0_task_switch_newcontext_post in Hs.
    sep_ex_elim_in Hs.
    asrt_to_line_in Hs 13.
    eapply sep_pure_l_elim in Hs.
    destruct Hs as [Hlgvl1 Hs].
    symmetry in Hlgvl1.
    inversion Hlgvl1; subst.
    sep_ex_intro.  
    eapply sep_pure_l_intro; eauto. 
    do 10 sep_cancel1 1 1.
    sep_cancel1 4 1.
    sep_cancel1 4 1.
    eapply sep_pure_l_intro; eauto.
    do 2 sep_cancel1 1 1.
    sep_cancel1 1 2.
    instantiate (1 := Aemp).
    eapply astar_emp_intro_r; eauto.
    eapply sep_pure_l_intro; eauto.
    introv Hct.
    destruct Hctx_win_save as [Hctx_win_save Hctx_pt_stk].
    split; eauto.
    split; eauto.
    Print stack_frame_save.
    instantiate (1 := (post_cwp id)).
    instantiate (1 := oid).
    instantiate (2 := F).
    instantiate (1 := fmo). 
    eapply stack_frame_match_fm_save; eauto.
    simpljoin1; eauto.
    simpljoin1; eauto.
    eapply in_range_0_7_post_cwp_still; eauto.

  introv Hnjp.
  clear Hiszero Heq7.
  assert (Hlen_clfp1 : length clfp1 < 8).
  {
    destruct Hstk_fm_match as [Hstk_fm_match Hlen_F].
    eapply stk_fm_match_stk_len_lt_13 with (id := id) (oid := oid); eauto.
    rewrite app_length; eauto.
    simpl; omega.
  }

  unfold iszero in Hnjp.
  destruct (Int.eq_dec (($ 1) <<ᵢ (post_cwp id)) &ᵢ (($ 1) <<ᵢ vi) $ 0); tryfalse.
  renames e to Hneq.
  eapply and_zero_not_eq in Hneq; eauto.
  inversion Hstk_fm_constraint; tryfalse; subst.
  match goal with
  | H1 : stack_frame_constraint' _ (post_cwp id) _ _ _,
         H2 : get_frame_nth _ 6 = Some (get_stk_addr _), H3 : _ = get_stk_cont _  |- _ =>
    renames H1 to Hstk_fm_constraint1, H2 to Hpt_stk, H3 to Hlfp
  end.
  simpl in Hlfp.
  subst clfp2.
  renames lfp to clfp2.
  simpl get_frame_nth in Hpt_stk.
  unfold get_stk_addr in Hpt_stk.
  unfold get_stk_addr in Hstk_fm_constraint1.
  assert (Hval_sp : w29 = cl -ᵢ ($ (64 * Z.of_nat (length clfp1)))).
  {
    inversion Hpt_stk; subst; eauto.
  }

  (** restore *)
  hoare_lift_pre 4.
  unfold FrameState at 1.
  eapply backward_rule.
  introv Hs.
  asrt_to_line_in Hs 3.
  simpl_sep_liftn_in Hs 4.
  eapply sep_pure_l_elim in Hs.
  destruct Hs as [_ Hs].
  eauto.
  hoare_lift_pre 3.
  eapply Pure_intro_rule.
  introv Hlen_F'.
  hoare_lift_pre 2.
  hoare_lift_pre 3.
  do 2 (destruct F'; simpl in Hlen_F'; tryfalse).
  eapply seq_rule.
  TimReduce_simpl.
  eapply restore_rule_reg; eauto.
  simpl; eauto.
  unfold win_masked.
  destruct (((($ 1) <<ᵢ (post_cwp id)) &ᵢ (($ 1) <<ᵢ vi)) !=ᵢ ($ 0)) eqn:Heqe; tryfalse; eauto.
  unfold negb in Heqe.
  destruct (((($ 1) <<ᵢ (post_cwp id)) &ᵢ (($ 1) <<ᵢ vi)) =ᵢ ($ 0)) eqn:Heqe1; tryfalse.
  eapply int_eq_false_neq in Heqe1; eauto.
  eapply and_not_zero_eq in Heqe1; tryfalse.
  eapply in_range_0_7_post_cwp_still; eauto.
  eauto. 
  simpl upd_genreg.
  subst w29.

  hoare_lift_pre 12.
  unfold stack at 1.
  eapply backward_rule.
  introv Hs.
  eapply stack'_split in Hs.
  simpl_sep_liftn_in Hs 2.
  unfold stack' in Hs; fold stack' in Hs.
  eapply astar_assoc_elim in Hs; eauto.
  omega.

  destruct fml', fmi'.
  destruct f, f0.
  hoare_lift_pre 4.

  (** st l0 (sp + OS_CPU_STACK_FRSME_L0_OFFSET) *)
  eapply seq_rule.
  TimReduce_simpl.
  eapply st_rule_save_stk_l0; eauto.
  simpl update_frame.

  (** st l1 (sp + OS_CPU_STACK_FRSME_L1_OFFSET) *)
  eapply seq_rule.
  TimReduce_simpl.
  eapply st_rule_save_stk_l1; eauto.
  simpl update_frame.

  (** st l2 (sp + OS_CPU_STACK_FRSME_L2_OFFSET) *)
  eapply seq_rule.
  TimReduce_simpl.
  eapply st_rule_save_stk_l2; eauto.
  simpl update_frame.

  (** st l3 (sp + OS_CPU_STACK_FRSME_L3_OFFSET) *)
  eapply seq_rule.
  TimReduce_simpl.
  eapply st_rule_save_stk_l3; eauto.
  simpl update_frame.

  (** st l4 (sp + OS_CPU_STACK_FRSME_L4_OFFSET) *)
  eapply seq_rule.
  TimReduce_simpl.
  eapply st_rule_save_stk_l4; eauto.
  simpl update_frame.

  (** st l5 (sp + OS_CPU_STACK_FRSME_L5_OFFSET) *)
  eapply seq_rule.
  TimReduce_simpl.
  eapply st_rule_save_stk_l5; eauto.
  simpl update_frame.

  (** st l6 (sp + OS_CPU_STACK_FRSME_L6_OFFSET) *)
  eapply seq_rule.
  TimReduce_simpl.
  eapply st_rule_save_stk_l6; eauto.
  simpl update_frame.

  (** st l7 (sp + OS_CPU_STACK_FRSME_L7_OFFSET) *)
  eapply seq_rule.
  TimReduce_simpl.
  eapply st_rule_save_stk_l7; eauto.
  simpl update_frame.

  (** st i0 (sp + OS_CPU_STACK_FRSME_I0_OFFSET) *)
  eapply seq_rule.
  TimReduce_simpl.
  eapply st_rule_save_stk_i0; eauto.
  simpl update_frame.

  (** st i1 (sp + OS_CPU_STACK_FRSME_I1_OFFSET) *)
  eapply seq_rule.
  TimReduce_simpl.
  eapply st_rule_save_stk_i1; eauto.
  simpl update_frame.

  (** st i2 (sp + OS_CPU_STACK_FRSME_I2_OFFSET) *)
  eapply seq_rule.
  TimReduce_simpl.
  eapply st_rule_save_stk_i2; eauto.
  simpl update_frame.

  (** st i3 (sp + OS_CPU_STACK_FRSME_i3_OFFSET) *)
  eapply seq_rule.
  TimReduce_simpl.
  eapply st_rule_save_stk_i3; eauto.
  simpl update_frame.

  (** st i4 (sp + OS_CPU_STACK_FRSME_I4_OFFSET) *)
  eapply seq_rule.
  TimReduce_simpl.
  eapply st_rule_save_stk_i4; eauto.
  simpl update_frame.

  (** st i5 (sp + OS_CPU_STACK_FRSME_I5_OFFSET) *)
  eapply seq_rule.
  TimReduce_simpl.
  eapply st_rule_save_stk_i5; eauto.
  simpl update_frame.

  (** st i6 (sp + OS_CPU_STACK_FRSME_I6_OFFSET) *)
  eapply seq_rule.
  TimReduce_simpl.
  eapply st_rule_save_stk_i6; eauto.
  simpl update_frame.

  (** st i7 (sp + OS_CPU_STACK_FRSME_I7_OFFSET) *)
  eapply seq_rule.
  TimReduce_simpl.
  eapply st_rule_save_stk_i7; eauto.
  simpl update_frame.
 
  hoare_lift_pre 5.
  hoare_lift_pre 6.
  eapply backward_rule.
  introv Hs.
  eapply FrameState_combine in Hs; eauto.
  clear - Hlen_F'.
  rewrite app_length; simpl; omega.
  split; eauto.
  eapply in_range_0_7_post_cwp_still; eauto.

  (** jmpl Ta0_save_usedwindows g0; nop *)
  eapply J1_rule; eauto.
  {
    TimReduce_simpl.
    introv Hs.
    simpl.
    unfold Ta0_save_usedwindows at 1 2.
    unfold Ta0_save_usedwindows at 1 2.
    rewrite in_range228; eauto.
  }
  {
    eval_spec.
  }
  {
    TimReduce_simpl.
    introv Hs.
    simpl_sep_liftn_in Hs 2.
    eapply GenRegs_split_one with (rr := g0) in Hs; eauto.
  }
  {
    TimReduce_simpl.
    eapply nop_rule; eauto.
    introv Hs.
    eapply GenRegs_upd_combine_one in Hs; eauto.
    remember (cl -ᵢ ($ (64 * Z.of_nat (length clfp1)))) as w29'.
    simpl upd_genreg in Hs.
    subst w29'.
    unfold ta0_save_usedwindows_pre.
    sep_ex_intro.
    asrt_to_line 20.
    eapply sep_pure_l_intro; eauto.
    simpl_sep_liftn 2.
    eapply GenRegs_split_Regs_Global.
    sep_cancel1 1 1.
    sep_cancel1 1 1.
    sep_cancel1 6 1.
    sep_cancel1 5 1.
    sep_cancel1 4 1.
    do 5 sep_cancel1 4 1.
    sep_cancel1 4 2.
    sep_cancel1 4 2.
    match goal with
    | H : _ |= _ |- _ => renames H to Hs
    end.
    simpl_sep_liftn_in Hs 3.
    eapply stack'_cons_tail in Hs; eauto.
    eapply stack'_app in Hs; eauto.
    sep_cancel1 1 1.
    instantiate (1 := Aemp).
    eapply astar_emp_intro_r; eauto.

    eapply sep_pure_l_intro; eauto.

    eapply sep_pure_l_intro.
    {
      instantiate (1 := F).
      instantiate (1 := fmo).
      instantiate (1 := oid).
      destruct Hstk_fm_match as [Hstk_fm_match Hlen_F].
      split; eauto.
      Print frame_restore.
 
      Lemma stk_fm_match_cons_tail_stable :
        forall F F' oid id lfp fmo fmo' fml fml' fmi fmi' fm1 fm2,
          $ 0 <=ᵤᵢ oid <=ᵤᵢ $ 7 -> $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 ->
          length F = 13 -> length F' = 11 ->
          stack_frame_match oid lfp (F ++ fmo :: nil) id ->
          frame_restore oid (fmo :: fml :: fmi :: F) id
                        (fmo' :: fml' :: fmi' :: F') ->
          stack_frame_match oid (lfp ++ (fm1, fm2) :: nil) (F ++ fmo :: nil) (post_cwp id).
      Proof.
        intros.
        do 14 (try destruct F; simpl in H1; tryfalse).
    }
  }
  
  >>>>>>>>>>>>>>>>>>>>>>>>