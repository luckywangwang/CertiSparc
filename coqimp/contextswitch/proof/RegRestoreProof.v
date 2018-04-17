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

Theorem RegRestoreProof :
  forall vl,
    spec |- {{ reg_restore_pre vl }}
             regstore
           {{ reg_restore_post vl }}.
Proof.
  intros.
  unfold reg_restore_pre.
  unfold reg_restore_post.
  hoare_ex_intro_pre.
  renames x' to fmg, x'0 to fmo, x'1 to fml, x'2 to fmi.
  renames x'3 to nctx, x'5 to vy, x'7 to id, x'8 to vi, x'9 to F.
  renames x'4 to l, x'6 to retl.
  eapply Pure_intro_rule.
  introv Hlgvl.
  destruct nctx as [nl nctx].
  destruct nctx as [ [ [rl ri] rg] ry].
  hoare_lift_pre 5.
  eapply Pure_intro_rule.
  introv Hpure.
  destruct Hpure as [Hsp [Hctx_addr Hretf] ].
  simpl in Hctx_addr.
  inversion Hctx_addr; subst.
  unfold regstore.
  hoare_lift_pre 2.
  unfold context at 1.
  unfold context'.
  eapply backward_rule.
  introv Hs.
  asrt_to_line_in Hs 3.
  eauto.
 
  save_reg_unfold.
  hoare_lift_pre 2.
  save_reg_unfold.
  hoare_lift_pre 3.
  save_reg_unfold.
  eapply backward_rule.
  introv Hs.
  unfold save_reg at 1 in Hs.
  asrt_to_line_in Hs 8.
  simpl_sep_liftn_in Hs 9.
  simpl_sep_liftn_in Hs 9.
  unfold save_reg at 1 in Hs.
  asrt_to_line_in Hs 8.
  simpl_sep_liftn_in Hs 9.
  simpl_sep_liftn_in Hs 17.
  unfold save_reg at 1 in Hs.
  asrt_to_line_in Hs 4.
  simpl_sep_liftn_in Hs 5.
  simpl_sep_liftn_in Hs 22.
  eauto.

  Ltac solve_ld_ctx :=
    eapply seq_rule;
    [TimReduce_simpl; eapply ld_rule_reg; eauto;
    try solve [simpl; repeat (rewrite Int.add_assoc); eauto] | simpl upd_genreg].

  destruct fmg, fmo, fml, fmi.
  simpl in Hsp.
  inversion Hsp; subst.
  
  (** ld (l5 + OS_L0_OFFSET) l0 *)
  solve_ld_ctx.
  simpl.
  unfold OS_L0_OFFSET.
  rewrite in_range0; eauto.
  rewrite Int.add_zero; eauto.
 
  (** ld (l5 + OS_L1_OFFSET) l1 *)
  hoare_lift_pre 3.
  hoare_lift_pre 2.
  solve_ld_ctx.

  (** ld (l5 + OS_L2_OFFSET) l2 *)
  hoare_lift_pre 4.
  hoare_lift_pre 2.
  solve_ld_ctx.

  (** ld (l5 + OS_L3_OFFSET) l3 *)
  hoare_lift_pre 5.
  hoare_lift_pre 2.
  solve_ld_ctx.

  (** ld (l5 + OS_I0_OFFSET) i0 *)
  hoare_lift_pre 6.
  hoare_lift_pre 2.
  solve_ld_ctx.

  (** ld (l5 + OS_I1_OFFSET) i1 *)
  hoare_lift_pre 7.
  hoare_lift_pre 2.
  solve_ld_ctx.

  (** ld (l5 + OS_I2_OFFSET) i2 *)
  hoare_lift_pre 8.
  hoare_lift_pre 2.
  solve_ld_ctx.

  (** ld (l5 + OS_I3_OFFSET) i3 *)
  hoare_lift_pre 9.
  hoare_lift_pre 2.
  solve_ld_ctx.

  (** ld (l5 + OS_I4_OFFSET) i4 *)
  hoare_lift_pre 10.
  hoare_lift_pre 2.
  solve_ld_ctx.

  (** ld (l5 + OS_I5_OFFSET) i5 *)
  hoare_lift_pre 11.
  hoare_lift_pre 2.
  solve_ld_ctx.

  (** ld (l5 + OS_I6_OFFSET) i6 *)
  hoare_lift_pre 12.
  hoare_lift_pre 2.
  solve_ld_ctx.

  (** ld (l5 + OS_I7_OFFSET) i7 *)
  hoare_lift_pre 13.
  hoare_lift_pre 2.
  solve_ld_ctx.

  (** ld (l5 + OS_Y_OFFSET) l6 *)
  hoare_lift_pre 22.
  hoare_lift_pre 2.
  solve_ld_ctx.

  (** wr l6 0 Ry *)
  hoare_lift_pre 23.
  hoare_lift_pre 2.
  eapply seq_rule.
  TimReduce_simpl.
  eapply wr_rule_reg; eauto.
  simpl; eauto.
  rewrite in_range0; eauto.
  simpl set_spec_reg.
  rewrite Int.xor_zero.

  (** ld (l5 + OS_G1_OFFSET) g1 *)
  hoare_lift_pre 17.
  hoare_lift_pre 2.
  solve_ld_ctx.

  (** ld (l5 + OS_G2_OFFSET) g2 *)
  hoare_lift_pre 18.
  hoare_lift_pre 2.
  solve_ld_ctx.

  (** ld (l5 + OS_G3_OFFSET) g3 *)
  hoare_lift_pre 19.
  hoare_lift_pre 2.
  solve_ld_ctx.

  (** ld (l5 + OS_G4_OFFSET) g4 *)
  hoare_lift_pre 20.
  hoare_lift_pre 2.
  solve_ld_ctx.

  (** ld (l5 + OS_G5_OFFSET) g5 *)
  hoare_lift_pre 21.
  hoare_lift_pre 2.
  solve_ld_ctx.

  (** ld (l5 + OS_G6_OFFSET) g6 *)
  hoare_lift_pre 22.
  hoare_lift_pre 2.
  solve_ld_ctx.

  (** ld (l5 + OS_G7_OFFSET) g7 *)
  hoare_lift_pre 23.
  hoare_lift_pre 2.
  solve_ld_ctx.

  (** retl; nop *)
  eapply retl_rule; eauto.
  TimReduce_simpl.
  eapply nop_rule; eauto.
  introv Hs.
  sep_ex_intro.
  eapply sep_pure_l_intro; eauto.
  sep_cancel1 1 1.
  sep_cancel1 8 2.
  unfold context, context'.
  asrt_to_line 4.
  unfold save_reg.
  asrt_to_line 4.
  simpl_sep_liftn 5.
  simpl_sep_liftn 5.
  asrt_to_line 8.
  simpl_sep_liftn 9.
  simpl_sep_liftn 13.
  asrt_to_line 8.
  simpl_sep_liftn 9.

  sep_cancel1 1 8.
  sep_cancel1 1 7.
  sep_cancel1 1 6.
  sep_cancel1 1 5.
  sep_cancel1 1 4.
  sep_cancel1 1 3.
  sep_cancel1 1 2.
  sep_cancel1 1 14.
  sep_cancel1 13 1.
  sep_cancel1 1 8.
  sep_cancel1 1 7.
  sep_cancel1 1 6.
  sep_cancel1 1 5.
  sep_cancel1 1 4.
  sep_cancel1 1 3.
  sep_cancel1 1 2.
  sep_cancel1 1 1.
  sep_cancel1 1 4.
  sep_cancel1 1 3.
  sep_cancel1 1 2.
  sep_cancel1 1 1.
  sep_cancel1 1 1.
  instantiate (1 := Aemp).
  eapply astar_emp_intro_r; eauto.
  eapply astar_emp_elim_r.
  eapply sep_pure_l_intro; eauto.
  simpls.
  repeat (split; eauto).

  unfold fretSta.
  TimReduce_simpl.
  introv Hs Hs'.
  simpl in Hretf.
  inversion Hretf; subst.
  sep_ex_elim_in Hs'.
  eapply sep_pure_l_elim in Hs'.
  destruct Hs' as [Hlgvl1 Hs'].
  inversion Hlgvl1; subst.
  destruct x, x0, x1, x2.
  simpl_sep_liftn_in Hs' 5.
  eapply sep_pure_l_elim in Hs'.
  destruct Hs' as [Hctx_win_restore Hs'].
  destruct_state s.
  destruct_state s'.
  eapply getR_eq_get_genreg_val1 with (rr := r15) in Hs; eauto.
  eapply getR_eq_get_genreg_val1 with (rr := r15) in Hs'; eauto.
  clear - Hs Hctx_win_restore Hs'.
  simpls.
  simpljoin1.
  unfolds get_R.
  destruct (r r15); tryfalse.
  destruct (r0 r15); tryfalse.
  inversion H0; subst.
  eauto.
Qed.

  
