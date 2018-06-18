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
Require Import spec.

Open Scope nat.
Open Scope code_scope.
Open Scope mem_scope.

Definition spec := convert_spec nil.

Lemma get_frm_nth_to_nth' :
  forall fm n x,
    get_frame_nth fm n = Some x ->
    get_frame_nth' fm n = x.
Proof.
  intros.
  destruct fm.
  do 8
     (destruct n; simpls;
      inversion H; eauto).
Qed.

Lemma frm_get_upd :
  forall fm n x,
    0 <= n <= 7 -> 
    get_frame_nth' (update_frame fm n x) n = x.
Proof.
  intros.
  destruct fm.
  do 8 (destruct n; simpl; eauto).
  omega.
Qed.

Theorem ChangeYProof :
  forall vl,
    spec |- {{ changeY_pre vl }}
             f # funChangeY
           {{ changeY_post vl }}.
Proof.
  intros.
  unfold changeY_pre.
  unfold changeY_post.  
  hoare_ex_intro_pre.
  renames x' to fmg, x'0 to fmo, x'1 to fml, x'2 to fmi.
  renames x'5 to vy, x'6 to vi, x'7 to id, x'8 to fm1, x'9 to fm2, x'10 to F.
  renames x'3 to fret, x'4 to x.
  eapply Pure_intro_rule; intros.

  hoare_lift_pre 5.
  eapply Pure_intro_rule.
  introv Hpure.
  simpljoin1.

  unfold funChangeY.

  (** rd Ry l0 *)
  eapply seq_rule.
  ins_tm_reduce_bas.
  eapply rd_rule_reg; eauto.
  simpl upd_genreg.

  (** wr i0 0 Ry *)
  eapply seq_rule.
  ins_tm_reduce_bas.
  eapply wr_rule_reg; eauto.
  simpl.
  rewrite in_range0; eauto.
  simpl set_spec_reg.
  rewrite Int.xor_zero.

  (** nop *)
  eapply seq_rule.
  ins_tm_reduce_bas.
  eapply nop_rule; eauto.

  (** nop *)
  eapply seq_rule.
  ins_tm_reduce_bas.
  eapply nop_rule; eauto.

  (** nop *)
  eapply seq_rule.
  ins_tm_reduce_bas.
  eapply nop_rule; eauto.

  (** restore l0 0 o0 *)
  hoare_lift_pre 4.
  hoare_lift_pre 4.
  hoare_lift_pre 3.
  eapply seq_rule.
  ins_tm_reduce_bas.
  eapply restore_rule_reg; eauto.
  simpl.
  rewrite in_range0; eauto.
  simpl upd_genreg.
  rewrite Int.add_zero.

  (** retl ;; nop *)
  eapply retl_rule.
  ins_tm_reduce_bas.
  ins_tm_reduce_bas.
  eapply nop_rule; eauto.

  introv Hs.
  sep_ex_intro. 
  sep_cancel1 1 2.
  sep_cancel1 3 2.
  sep_cancel1 1 2.
  sep_cancel1 1 2.
  instantiate (1 := Aemp).
  eapply astar_emp_intro_r.
  eauto.
  eapply sep_pure_l_intro.
  eauto. 
  erewrite get_frm_nth_to_nth'.
  rewrite frm_get_upd; eauto.
  omega.
  eauto.
  eauto.
  unfold fretSta.
  introv Hs Hs'.
  eapply asrt_time_reduce in Hs.
  rewrite tmreduce_TimReduce in Hs.
  eapply asrt_time_reduce in Hs.
  do 2 rewrite GenRegs_TimeReduce in Hs.
  TimReduce_simpl_in_bas Hs.

  eapply GenRegs_split_one with (rr := r15) in Hs.
  simpl get_genreg_val' in Hs.
  eapply GenRegs_split_one with (rr := r15) in Hs'.
  simpl get_genreg_val' in Hs'.
  clear - Hs Hs'.
  destruct_state s.
  destruct_state s'.
  eapply rn_st_v_eval_reg_v in Hs.
  eapply rn_st_v_eval_reg_v in Hs'.
  simpl.
  eauto.
Qed.
