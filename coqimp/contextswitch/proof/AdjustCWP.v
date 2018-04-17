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
  
(*+ Proof +*)
Theorem Ta0AdjustCWPProof :
  forall vl,
    spec |- {{ ta0_adjust_cwp_pre vl }}
             ta0_adjust_cwp
           {{ ta0_adjust_cwp_post vl }}.
Proof.
  intros.
  unfold ta0_adjust_cwp_pre.
  unfold ta0_adjust_cwp_post.
  hoare_ex_intro_pre.
  renames x' to fmg, x'0 to fmo, x'1 to fml, x'2 to fmi.
  renames x'3 to id, x'6 to vi, x'4 to F, x'5 to vy. 
  renames x'8 to i, x'13 to vz, x'14 to vn.
  renames x'7 to ll, x'9 to ct, x'10 to nt, x'11 to nctx, x'12 to nstk, x'15 to oid.
  eapply Pure_intro_rule.
  introv Hlgvl.
  hoare_lift_pre 13.
  eapply Pure_intro_rule.
  introv Hpure.
  hoare_lift_pre 13.
  eapply Pure_intro_rule.
  introv Hnctx.
  destruct fmg, fmo, fml, fmi.
  eapply backward_rule.
  introv Hs.
  simpl_sep_liftn_in Hs 2.
  eapply Regs_Global_combine_GenRegs in Hs; eauto.
  unfold ta0_adjust_cwp.

  destruct Hpure as [Hg4 [Hrot [Hoid_range [Hvl_g4 [Hg7 Hct] ] ] ] ].
  simpl in Hg4.
  inversion Hg4; subst.
  simpl in Hg7.
  inversion Hg7; subst.

  (** sll g4 1 g5 *)
  eapply seq_rule.
  TimReduce_simpl.
  eapply sll_rule_reg; eauto.
  simpl; eauto.
  rewrite in_range1; eauto.
  simpl upd_genreg.

  (** srl g4 (OS_WINDOWS - 1) g5 *)
  unfold OS_WINDOWS.
  assert (Heq7 : ($ 8) -ᵢ ($ 1) = ($ 7)).
  eauto.
  rewrite Heq7.
  eapply seq_rule.
  TimReduce_simpl.
  eapply srl_rule_reg; eauto.
  simpl; eauto.
  rewrite in_range7; eauto.
  simpl upd_genreg. 
  rewrite get_range_0_4_stable; eauto.
  rewrite get_range_0_4_stable; eauto.
  
  (** or g4 g5 g4 *)
  eapply seq_rule.
  TimReduce_simpl.
  eapply or_rule_reg; eauto.
  simpl; eauto. 
  simpl upd_genreg.

  eapply hoare_pure_gen' with (pu := $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 /\ $ 0 <=ᵤᵢ vi <=ᵤᵢ $ 7).
  {
    introv Hs.
    simpl_sep_liftn_in Hs 2.
    unfold FrameState in Hs.
    asrt_to_line_in Hs 3.
    simpl_sep_liftn_in Hs 4.
    eapply sep_pure_l_elim in Hs; eauto.
    simpljoin1; eauto.
  } 
  eapply Pure_intro_rule.
  introv Hid_inrange.
  destruct Hid_inrange as [Hid_inrange Hvi_inrange].
    
  (** andcc g4 g7 g0 *)
  hoare_lift_pre 4.
  hoare_lift_pre 5.
  hoare_lift_pre 3.
  eapply seq_rule.
  TimReduce_simpl. 
  eapply andcc_rule_reg; eauto.
  simpl upd_genreg.
  simpl get_genreg_val.
  assert (Hiszero : iszero ((i >>ᵢ ($ 7)) |ᵢ (i <<ᵢ ($ 1))) &ᵢ (($ 1) <<ᵢ vi) =
         iszero (get_range 0 7 ((i >>ᵢ ($ 7)) |ᵢ (i <<ᵢ ($ 1)))) &ᵢ (($ 1) <<ᵢ vi)).
  {
    rewrite in_range_0_7_and; eauto.
  }  
  rewrite Hiszero.
  rewrite g4_val_get_range_0_7_equal with (id := id); eauto.

  (** bne Ta0_Switch; nop *)
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
    simpl_sep_liftn_in Hs 3.
    sep_cancel1 1 1.
    simpl; eauto.
  }

  Focus 3.
  introv Hne.
  unfold iszero in Hne.
  destruct (Int.eq_dec (($ 1) <<ᵢ (post_cwp id)) &ᵢ (($ 1) <<ᵢ vi) $ 0); tryfalse.
  clear Hne.
  renames n to Hne.
  eapply and_not_zero_eq in Hne; eauto.
  2 : eapply in_range_0_7_post_cwp_still; eauto.
  split.
 
    introv Hs.
    unfold ta0_task_switch_newcontext_pre.
    sep_ex_intro.
    asrt_to_line 14.
    eapply sep_pure_l_intro; eauto.
    simpl_sep_liftn 2.
    eapply GenRegs_split_Regs_Global; eauto.
    sep_cancel1 1 1.
    sep_cancel1 3 1.
    sep_cancel1 1 3.
    sep_cancel1 1 2.
    do 7 sep_cancel1 1 1.
    instantiate (1 := Aemp).
    eapply astar_emp_intro_r; eauto.
    instantiate (1 := Aemp).
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
    do 12 sep_cancel1 1 1.
    match goal with
    | H : _ |= _ |- _ => renames H to Hs
    end.
    eapply sep_pure_l_elim in Hs; eauto.

  2 : DlyFrameFree_elim.  

  introv Heq.
  unfold iszero in Heq.
  destruct (Int.eq_dec (($ 1) <<ᵢ (post_cwp id)) &ᵢ (($ 1) <<ᵢ vi) $ 0); tryfalse.
  clear Heq.
  renames e to Heq.
  eapply and_zero_not_eq in Heq; eauto.
  2 : eapply in_range_0_7_post_cwp_still; eauto.

  eapply hoare_pure_gen' with (length F = 13).
  {
    introv Hs.
    simpl_sep_liftn_in Hs 4.
    unfold FrameState in Hs.
    asrt_to_line_in Hs 3.
    simpl_sep_liftn_in Hs 3.
    eapply sep_pure_l_elim in Hs.
    simpljoin1; eauto.
  }
  eapply Pure_intro_rule.
  introv Hlen_F.

  destruct F; simpl in Hlen_F; tryfalse.
  destruct F; simpl in Hlen_F; tryfalse.
  destruct f, f0.
  hoare_lift_pre 4. 
  unfold FrameState at 1.
  eapply backward_rule.
  introv Hs.
  asrt_to_line_in Hs 3.
  simpl_sep_liftn_in Hs 3.
  eapply sep_pure_l_elim in Hs.
  destruct Hs as [_ Hs].
  simpl_sep_liftn_in Hs 3.
  eapply sep_pure_l_elim in Hs.
  destruct Hs as [_ Hs].
  eauto.

  (** restore *)
  hoare_lift_pre 2.
  hoare_lift_pre 3.
  eapply seq_rule; eauto.
  TimReduce_simpl.
  eapply restore_rule_reg; eauto.
  simpl; eauto.
  unfold win_masked.
  destruct (((($ 1) <<ᵢ (post_cwp id)) &ᵢ (($ 1) <<ᵢ vi)) !=ᵢ ($ 0)) eqn:Heqe; eauto.
  unfold negb in Heqe.
  destruct (((($ 1) <<ᵢ (post_cwp id)) &ᵢ (($ 1) <<ᵢ vi)) =ᵢ ($ 0)) eqn:Heqe1; tryfalse.
  eapply int_eq_false_neq in Heqe1.
  eapply and_not_zero_eq in Heqe1; eauto.
  subst; tryfalse.
  eapply in_range_0_7_post_cwp_still; eauto.
  simpl upd_genreg.

  (** jumpl Ta0_adjust_cwp; nop *)
  eapply J1_rule; eauto.
  {
    TimReduce_simpl.
    introv Hs.
    simpl. 
    unfold Ta0_adjust_CWP at 1 2.
    unfold Ta0_adjust_CWP at 1 2.
    rewrite in_range344; eauto.
  }
  {
    eval_spec.
  }
  {
    TimReduce_simpl.
    introv Hs.
    eapply GenRegs_split_one with (rr := g0) in Hs.
    simpl get_genreg_val' in Hs.
    eauto.
  }
  {
    TimReduce_simpl.
    eapply nop_rule; eauto.
    introv Hs.
    eapply GenRegs_upd_combine_one in Hs.
    simpl upd_genreg in Hs.
    simpl_sep_liftn_in Hs 2.
    simpl_sep_liftn_in Hs 3.
    eapply FrameState_combine in Hs; eauto.
    unfold ta0_adjust_cwp_pre.
    sep_ex_intro.
    asrt_to_line 14.
    eapply sep_pure_l_intro; eauto.
    simpl_sep_liftn 2.
    eapply GenRegs_split_Regs_Global; eauto.
    sep_cancel1 2 1.
    sep_cancel1 4 2.
    sep_cancel1 1 1.
    sep_cancel1 1 2.
    do 7 sep_cancel1 1 1.
    instantiate (1 := Aemp).
    eapply astar_emp_intro_r; eauto.
    instantiate (1 := Aemp).
    simpl get_frame_nth.
    eapply sep_pure_l_intro; eauto.
    split; eauto.
    split.
    {
      instantiate (1 := oid).
      eapply rotate_cons; eauto.
    }
    repeat (split; eauto).
    eapply g4_rot_stable with (oid := oid); eauto.
    eapply sep_pure_l_intro; eauto.
    clear - Hlen_F.
    rewrite app_length.
    simpl; omega.
    split; eauto.
    eapply in_range_0_7_post_cwp_still; eauto.
  }

  introv Hs.
  unfold ta0_adjust_cwp_post in Hs.
  sep_ex_elim_in Hs.
  asrt_to_line_in Hs 13.
  sep_ex_intro.
  do 13 sep_cancel1 1 1.
  match goal with
  | H : _ |= _ |- _ => rename H into Hs
  end.
  eapply sep_pure_l_elim in Hs; eauto.

  DlyFrameFree_elim.
Qed.