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