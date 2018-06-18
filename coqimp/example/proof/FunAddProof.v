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

Theorem FunAddProof :
  forall vl,
    spec |- {{ add_pre vl }}
             f # funcadd
           {{ add_post vl }}.
Proof.
  intros.
  unfold add_pre.
  unfold add_post.
  hoare_ex_intro_pre.
  renames x' to x, x'0 to y, x'1 to z, x'3 to fret.
  eapply Pure_intro_rule; intros.
  unfold funcadd.

  (** add i0 i1 l7 *)
  eapply seq_rule.
  ins_tm_reduce_bas.
  eapply add_rule; eauto.
  introv Hs.
  split.
  {
    destruct_state s.
    eapply rn_st_v_eval_reg_v in Hs.
    simpl; eauto.
    unfold get_R.
    simpl; eauto.
    rewrite Hs; eauto.
  }
  {
    simpl_sep_liftn_in Hs 2.
    destruct_state s.
    eapply rn_st_v_eval_reg_v in Hs; eauto.
    simpl; eauto.
    unfold get_R.
    simpl; eauto.
    rewrite Hs; eauto.
  }
  introv Hs.
  simpl_sep_liftn_in Hs 4; eauto.

  (** add l7 i2 l7 *)
  eapply seq_rule.
  ins_tm_reduce_bas.
  eapply add_rule; eauto.
  introv Hs.
  split.
  {
    destruct_state s.
    eapply rn_st_v_eval_reg_v in Hs; eauto.
    simpl.
    unfold get_R.
    simpl; eauto.
    rewrite Hs; eauto.
  }
  {
    simpl_sep_liftn_in Hs 4.
    destruct_state s.
    eapply rn_st_v_eval_reg_v in Hs.
    simpl.
    unfold get_R.
    simpl; eauto.
    rewrite Hs; eauto.
  }

  (** retl ;; nop *)
  eapply retl_rule; eauto.
  ins_tm_reduce_bas.
  ins_tm_reduce_bas.
  eapply nop_rule; eauto.
  introv Hs.
  sep_ex_intro.
  eapply sep_pure_l_intro; eauto.
  sep_cancel1 2 1.
  sep_cancel1 2 1.
  sep_cancel1 2 1.
  eauto.

  unfold fretSta.
  introv Hs Hs'.
  eapply asrt_time_reduce in Hs.
  TimReduce_simpl_in_bas Hs.
  eapply asrt_time_reduce in Hs.
  TimReduce_simpl_in_bas Hs.
  simpl_sep_liftn_in Hs 5.
  sep_ex_elim_in Hs'. 
  eapply sep_pure_l_elim in Hs'.
  simpljoin1.
  symmetry in H0.
  inversion H0; eauto; subst.
  simpl_sep_liftn_in H1 5.
  destruct_state s.
  eapply rn_st_v_eval_reg_v in Hs; eauto.
  destruct_state s'.
  eapply rn_st_v_eval_reg_v in H1; eauto.
Qed.