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
Require Import derived_rule.

Require Import integer_lemma.

Require Import code.
Require Import ctxswitch_spec.

Open Scope nat.
Open Scope code_scope.
Open Scope mem_scope.

(*+ Trivial Lemmas +*)
Lemma len_neq_0_tail :
  forall {A : Type} (ls : list A),
    length ls > 0 -> exists a ls', ls = ls' ++ (a :: nil).
Proof.
  intros A ls.
  induction ls; intros.
  -
    simpls; tryfalse.
    omega.
  -
    destruct ls.
    exists a.
    eexists.
    instantiate (1 := nil).
    simpl; eauto.
    assert (length (a0 :: ls) > 0).
    simpl; eauto.
    omega.
    eapply IHls in H0.
    simpljoin1.
    exists x (a :: x0).
    simpl; eauto.
    rewrite H0.
    eauto.
Qed.

(*+ Lemmas for asrt +*)
Lemma asrt_disj_intro :
  forall p1 p2 s,
    s |= p1 \/ s |= p2 ->
    s |= p1 \\// p2.
Proof.
  intros.
  simpl.
  eauto.
Qed.

(*+ Lemmas for Rules +*)
Lemma rd_rule_reg_wim :
  forall (v id : Word) (rr : GenReg) (p : asrt) F (grst : GenRegState),
    |- {{GenRegs grst ** FrameState id v F ** p}} rd Rwim rr
      {{GenRegs (upd_genreg grst rr (($ 1) <<ᵢ v)) ** FrameState id v F ** p}}.
Proof.
  intros.
  eapply ins_conseq_rule.
  introv Hs. 
  simpl_sep_liftn_in Hs 2.
  unfold FrameState in Hs.
  eapply astar_assoc_elim in Hs.
  simpl_sep_liftn_in Hs 2.
  eapply astar_assoc_elim in Hs.
  simpl_sep_liftn_in Hs 4.
  eauto.
  eapply rd_rule_reg.
  introv Hs.
  sep_cancel1 1 1.
  unfold FrameState.
  eapply astar_assoc_intro.
  sep_cancel1 3 1.
  eapply astar_assoc_intro.
  sep_cancel1 1 1.
  eauto.
Qed.

Theorem save_rule_reg_frame :
  forall p (rs rd : GenReg) (id id' : Word) (F : FrameList)
    (fm1 fm2 fmg fmo fml fmi : Frame) (v1 v2 v v' : Word) (oexp : OpExp),
    get_genreg_val (fmg, fmo, fml, fmi) rs = v1 ->
    eval_opexp_reg (fmg, fmo, fml, fmi) oexp = Some v2 ->
    id' = pre_cwp id -> win_masked id' (($ 1) <<ᵢ v) = false ->
    |- {{ GenRegs (fmg, fmo, fml, fmi) ** FrameState id v (F ++ fm1 :: fm2 :: nil) ** p }}
        save rs oexp rd
        {{ GenRegs (upd_genreg (fmg, fm1, fm2, fmo) rd (v1 +ᵢ v2)) **
                   FrameState id' v (fml :: fmi :: F) ** p }}.
Proof.
  intros.
  eapply ins_conseq_rule.
  Focus 2.
  eapply save_rule_reg; eauto.
  {
    introv Hs.
    instantiate (4 := F).
    instantiate (3 := fm1).
    instantiate (2 := fm2).
    instantiate (1 := [|length (fml :: fmi :: F) = 13|]
                        ** [|$ 0 <=ᵤᵢ id' <=ᵤᵢ $ 7 /\ $ 0 <=ᵤᵢ v <=ᵤᵢ $ 7|] ** p).
    unfolds FrameState.
    sep_cancel1 1 1.
    eapply astar_assoc_elim in H3.
    sep_cancel1 1 2.
    eapply astar_assoc_elim in H4.
    sep_cancel1 1 1.
    eapply astar_assoc_elim in H3.
    eapply sep_pure_l_elim in H3.
    simpljoin1.
    eapply sep_pure_l_elim in H4.
    simpljoin1; eauto.
    eapply sep_pure_l_intro.
    rewrite app_length in H3.
    simpls.
    omega. 
    eapply sep_pure_l_intro; eauto.
    split; eauto.
    eapply in_range_0_7_pre_cwp_still; eauto.
  }
  {
    introv Hs.
    sep_cancel1 1 1.
    unfold FrameState.
    eapply astar_assoc_intro.
    sep_cancel1 2 1.
    eapply astar_assoc_intro.
    sep_cancel1 1 1.
    eapply astar_assoc_intro; eauto.
  }
Qed.

Lemma st_rule_save_stk_l0 :
  forall grst p l fm1 fm2 v1,
    get_genreg_val grst l0 = v1 ->
    get_genreg_val grst sp = l ->
    |- {{ GenRegs grst ** stack_frame l fm1 fm2 ** p }}
        st l0 (Aro sp (' 0))
      {{ GenRegs grst ** stack_frame l (update_frame fm1 0 v1) fm2 ** p }}.
Proof.
  intros.
  destruct fm1, fm2.
  eapply ins_conseq_rule.
  {
    introv Hs.
    simpl_sep_liftn_in Hs 2.
    unfold stack_frame in Hs.
    eapply astar_assoc_elim in Hs.
    unfold stack_seg at 1 in Hs.
    asrt_to_line_in Hs 7.
    simpl_sep_liftn_in Hs 10.    
    eauto.
  }
  { 
    eapply st_rule_reg.
    simpl.
    rewrite in_range0; eauto.
    rewrite H0; eauto.
    rewrite Int.add_zero; eauto.
    eauto.
  }
  {  
    introv Hs.
    simpl update_frame.
    unfold stack_frame.
    sep_cancel1 1 1.
    eapply astar_assoc_intro.
    sep_cancel1 9 2.
    unfold stack_seg.
    asrt_to_line 7. 
    sep_cancel1 1 1.
    eauto.
  }
Qed.

Lemma st_rule_save_stk_l1 :
  forall grst p l fm1 fm2 v1,
    get_genreg_val grst l1 = v1 ->
    get_genreg_val grst sp = l ->
    |- {{ GenRegs grst ** stack_frame l fm1 fm2 ** p }}
        st l1 (Aro sp (' 4))
      {{ GenRegs grst ** stack_frame l (update_frame fm1 1 v1) fm2 ** p }}.
Proof.
  intros.
  destruct fm1, fm2.
  eapply ins_conseq_rule.
  {
    introv Hs.
    simpl_sep_liftn_in Hs 2.
    unfold stack_frame in Hs.
    eapply astar_assoc_elim in Hs.
    unfold stack_seg at 1 in Hs.
    asrt_to_line_in Hs 7.
    simpl_sep_liftn_in Hs 2.
    simpl_sep_liftn_in Hs 10.    
    eauto.
  }
  { 
    eapply st_rule_reg.
    simpl.
    rewrite in_range4; eauto.
    rewrite H0; eauto.
    eauto.
  }
  {  
    introv Hs.
    simpl update_frame.
    unfold stack_frame.
    sep_cancel1 1 1.
    eapply astar_assoc_intro.
    sep_cancel1 9 2.
    unfold stack_seg.
    asrt_to_line 7.
    sep_cancel1 1 2.
    eauto.
  }
Qed.

Lemma st_rule_save_stk_l2 :
  forall grst p l fm1 fm2 v1,
    get_genreg_val grst l2 = v1 ->
    get_genreg_val grst sp = l ->
    |- {{ GenRegs grst ** stack_frame l fm1 fm2 ** p }}
        st l2 (Aro sp (' 8))
      {{ GenRegs grst ** stack_frame l (update_frame fm1 2 v1) fm2 ** p }}.
Proof.
  intros.
  destruct fm1, fm2.
  eapply ins_conseq_rule.
  {
    introv Hs.
    simpl_sep_liftn_in Hs 2.
    unfold stack_frame in Hs.
    eapply astar_assoc_elim in Hs.
    unfold stack_seg at 1 in Hs.
    asrt_to_line_in Hs 7.
    simpl_sep_liftn_in Hs 3.
    simpl_sep_liftn_in Hs 10.    
    eauto.
  }
  { 
    eapply st_rule_reg.
    simpl.
    rewrite in_range8; eauto.
    rewrite H0; eauto.
    eauto.
  }
  {  
    introv Hs.
    simpl update_frame.
    unfold stack_frame.
    sep_cancel1 1 1.
    eapply astar_assoc_intro.
    sep_cancel1 9 2.
    unfold stack_seg.
    asrt_to_line 7.
    sep_cancel1 1 3.
    eauto.
  }
Qed.

Lemma st_rule_save_stk_l3 :
  forall grst p l fm1 fm2 v1,
    get_genreg_val grst l3 = v1 ->
    get_genreg_val grst sp = l ->
    |- {{ GenRegs grst ** stack_frame l fm1 fm2 ** p }}
        st l3 (Aro sp (' 12))
      {{ GenRegs grst ** stack_frame l (update_frame fm1 3 v1) fm2 ** p }}.
Proof.
  intros.
  destruct fm1, fm2.
  eapply ins_conseq_rule.
  {
    introv Hs.
    simpl_sep_liftn_in Hs 2.
    unfold stack_frame in Hs.
    eapply astar_assoc_elim in Hs.
    unfold stack_seg at 1 in Hs.
    asrt_to_line_in Hs 7.
    simpl_sep_liftn_in Hs 4.
    simpl_sep_liftn_in Hs 10.    
    eauto.
  }
  { 
    eapply st_rule_reg.
    simpl.
    rewrite in_range12; eauto.
    rewrite H0; eauto.
    eauto.
  }
  {  
    introv Hs.
    simpl update_frame.
    unfold stack_frame.
    sep_cancel1 1 1.
    eapply astar_assoc_intro.
    sep_cancel1 9 2.
    unfold stack_seg.
    asrt_to_line 7.
    sep_cancel1 1 4.
    eauto.
  }
Qed.

Lemma st_rule_save_stk_l4 :
  forall grst p l fm1 fm2 v1,
    get_genreg_val grst l4 = v1 ->
    get_genreg_val grst sp = l ->
    |- {{ GenRegs grst ** stack_frame l fm1 fm2 ** p }}
        st l4 (Aro sp (' 16))
      {{ GenRegs grst ** stack_frame l (update_frame fm1 4 v1) fm2 ** p }}.
Proof.
  intros.
  destruct fm1, fm2.
  eapply ins_conseq_rule.
  {
    introv Hs.
    simpl_sep_liftn_in Hs 2.
    unfold stack_frame in Hs.
    eapply astar_assoc_elim in Hs.
    unfold stack_seg at 1 in Hs.
    asrt_to_line_in Hs 7.
    simpl_sep_liftn_in Hs 5.
    simpl_sep_liftn_in Hs 10.    
    eauto.
  }
  { 
    eapply st_rule_reg.
    simpl.
    rewrite in_range16; eauto.
    rewrite H0; eauto.
    eauto.
  }
  {  
    introv Hs.
    simpl update_frame.
    unfold stack_frame.
    sep_cancel1 1 1.
    eapply astar_assoc_intro.
    sep_cancel1 9 2.
    unfold stack_seg.
    asrt_to_line 7.
    sep_cancel1 1 5.
    eauto.
  }
Qed.

Lemma st_rule_save_stk_l5 :
  forall grst p l fm1 fm2 v1,
    get_genreg_val grst l5 = v1 ->
    get_genreg_val grst sp = l ->
    |- {{ GenRegs grst ** stack_frame l fm1 fm2 ** p }}
        st l5 (Aro sp (' 20))
      {{ GenRegs grst ** stack_frame l (update_frame fm1 5 v1) fm2 ** p }}.
Proof.
  intros.
  destruct fm1, fm2.
  eapply ins_conseq_rule.
  {
    introv Hs.
    simpl_sep_liftn_in Hs 2.
    unfold stack_frame in Hs.
    eapply astar_assoc_elim in Hs.
    unfold stack_seg at 1 in Hs.
    asrt_to_line_in Hs 7.
    simpl_sep_liftn_in Hs 6.
    simpl_sep_liftn_in Hs 10.    
    eauto.
  }
  { 
    eapply st_rule_reg.
    simpl.
    rewrite in_range20; eauto.
    rewrite H0; eauto.
    eauto.
  }
  {  
    introv Hs.
    simpl update_frame.
    unfold stack_frame.
    sep_cancel1 1 1.
    eapply astar_assoc_intro.
    sep_cancel1 9 2.
    unfold stack_seg.
    asrt_to_line 7.
    sep_cancel1 1 6.
    eauto.
  }
Qed.

Lemma st_rule_save_stk_l6 :
  forall grst p l fm1 fm2 v1,
    get_genreg_val grst l6 = v1 ->
    get_genreg_val grst sp = l ->
    |- {{ GenRegs grst ** stack_frame l fm1 fm2 ** p }}
        st l6 (Aro sp (' 24))
      {{ GenRegs grst ** stack_frame l (update_frame fm1 6 v1) fm2 ** p }}.
Proof.
  intros.
  destruct fm1, fm2.
  eapply ins_conseq_rule.
  {
    introv Hs.
    simpl_sep_liftn_in Hs 2.
    unfold stack_frame in Hs.
    eapply astar_assoc_elim in Hs.
    unfold stack_seg at 1 in Hs.
    asrt_to_line_in Hs 7.
    simpl_sep_liftn_in Hs 7.
    simpl_sep_liftn_in Hs 10.    
    eauto.
  }
  { 
    eapply st_rule_reg.
    simpl.
    rewrite in_range24; eauto.
    rewrite H0; eauto.
    eauto.
  }
  {  
    introv Hs.
    simpl update_frame.
    unfold stack_frame.
    sep_cancel1 1 1.
    eapply astar_assoc_intro.
    sep_cancel1 9 2.
    unfold stack_seg.
    asrt_to_line 7.
    sep_cancel1 1 7.
    eauto.
  }
Qed.

Lemma st_rule_save_stk_l7 :
  forall grst p l fm1 fm2 v1,
    get_genreg_val grst l7 = v1 ->
    get_genreg_val grst sp = l ->
    |- {{ GenRegs grst ** stack_frame l fm1 fm2 ** p }}
        st l7 (Aro sp (' 28))
      {{ GenRegs grst ** stack_frame l (update_frame fm1 7 v1) fm2 ** p }}.
Proof.
  intros.
  destruct fm1, fm2.
  eapply ins_conseq_rule.
  {
    introv Hs.
    simpl_sep_liftn_in Hs 2.
    unfold stack_frame in Hs.
    eapply astar_assoc_elim in Hs.
    unfold stack_seg at 1 in Hs.
    asrt_to_line_in Hs 7.
    simpl_sep_liftn_in Hs 8.
    simpl_sep_liftn_in Hs 10.    
    eauto.
  }
  { 
    eapply st_rule_reg.
    simpl.
    rewrite in_range28; eauto.
    rewrite H0; eauto.
    eauto.
  }
  {  
    introv Hs.
    simpl update_frame.
    unfold stack_frame.
    sep_cancel1 1 1.
    eapply astar_assoc_intro.
    sep_cancel1 9 2.
    unfold stack_seg.
    asrt_to_line 7.
    sep_cancel1 1 8.
    eauto.
  }
Qed.

Lemma st_rule_save_stk_i0 :
  forall grst p l fm1 fm2 v1, 
    get_genreg_val grst i0 = v1 ->
    get_genreg_val grst sp = l ->
    |- {{ GenRegs grst ** stack_frame l fm1 fm2 ** p }}
        st i0 (Aro sp (' 32))
      {{ GenRegs grst ** stack_frame l fm1 (update_frame fm2 0 v1) ** p }}.
Proof.
  intros.
  destruct fm1, fm2.
  eapply ins_conseq_rule.
  {
    introv Hs.
    simpl_sep_liftn_in Hs 2.
    unfold stack_frame in Hs.
    eapply astar_assoc_elim in Hs.
    simpl_sep_liftn_in Hs 2.
    unfold stack_seg at 1 in Hs.
    asrt_to_line_in Hs 7.
    simpl_sep_liftn_in Hs 10.    
    eauto.
  }
  { 
    eapply st_rule_reg.
    simpl.
    rewrite in_range32; eauto.
    rewrite H0; eauto.
    eauto.
  }
  {  
    introv Hs.
    simpl update_frame.
    unfold stack_frame.
    sep_cancel1 1 1.
    eapply astar_assoc_intro.
    sep_cancel1 9 1.
    unfold stack_seg.
    asrt_to_line 7.
    eauto.
  }
Qed.

Lemma st_rule_save_stk_i1 :
  forall grst p l fm1 fm2 v1,
    get_genreg_val grst i1 = v1 ->
    get_genreg_val grst sp = l ->
    |- {{ GenRegs grst ** stack_frame l fm1 fm2 ** p }}
        st i1 (Aro sp (' 36))
      {{ GenRegs grst ** stack_frame l fm1 (update_frame fm2 1 v1) ** p }}.
Proof.
  intros.
  destruct fm1, fm2.
  eapply ins_conseq_rule.
  {
    introv Hs.
    simpl_sep_liftn_in Hs 2.
    unfold stack_frame in Hs.
    eapply astar_assoc_elim in Hs.
    simpl_sep_liftn_in Hs 2.
    unfold stack_seg at 1 in Hs.
    asrt_to_line_in Hs 7.
    simpl_sep_liftn_in Hs 2.
    simpl_sep_liftn_in Hs 10.    
    eauto.
  }
  { 
    eapply st_rule_reg.
    simpl.
    rewrite in_range36; eauto.
    rewrite H0; eauto.
    rewrite Int.add_assoc.
    eauto.
    eauto.
  }
  {  
    introv Hs.
    simpl update_frame.
    unfold stack_frame.
    sep_cancel1 1 1.
    eapply astar_assoc_intro.
    sep_cancel1 9 1.
    unfold stack_seg.
    asrt_to_line 7. 
    sep_cancel1 1 2.
    eauto.
  }
Qed.

Lemma st_rule_save_stk_i2 :
  forall grst p l fm1 fm2 v1,
    get_genreg_val grst i2 = v1 ->
    get_genreg_val grst sp = l ->
    |- {{ GenRegs grst ** stack_frame l fm1 fm2 ** p }}
        st i2 (Aro sp (' 40))
      {{ GenRegs grst ** stack_frame l fm1 (update_frame fm2 2 v1) ** p }}.
Proof.
  intros.
  destruct fm1, fm2.
  eapply ins_conseq_rule.
  {
    introv Hs.
    simpl_sep_liftn_in Hs 2.
    unfold stack_frame in Hs.
    eapply astar_assoc_elim in Hs.
    simpl_sep_liftn_in Hs 2.
    unfold stack_seg at 1 in Hs.
    asrt_to_line_in Hs 7.
    simpl_sep_liftn_in Hs 3.
    simpl_sep_liftn_in Hs 10.    
    eauto.
  }
  { 
    eapply st_rule_reg.
    simpl.
    rewrite in_range40; eauto.
    rewrite H0; eauto.
    rewrite Int.add_assoc.
    eauto.
    eauto.
  }
  {  
    introv Hs.
    simpl update_frame.
    unfold stack_frame.
    sep_cancel1 1 1.
    eapply astar_assoc_intro.
    sep_cancel1 9 1.
    unfold stack_seg.
    asrt_to_line 7. 
    sep_cancel1 1 3. 
    eauto.
  }
Qed.

Lemma st_rule_save_stk_i3 :
  forall grst p l fm1 fm2 v1,
    get_genreg_val grst i3 = v1 ->
    get_genreg_val grst sp = l ->
    |- {{ GenRegs grst ** stack_frame l fm1 fm2 ** p }}
        st i3 (Aro sp (' 44))
      {{ GenRegs grst ** stack_frame l fm1 (update_frame fm2 3 v1) ** p }}.
Proof.
  intros.
  destruct fm1, fm2.
  eapply ins_conseq_rule.
  {
    introv Hs.
    simpl_sep_liftn_in Hs 2.
    unfold stack_frame in Hs.
    eapply astar_assoc_elim in Hs.
    simpl_sep_liftn_in Hs 2.
    unfold stack_seg at 1 in Hs.
    asrt_to_line_in Hs 7.
    simpl_sep_liftn_in Hs 4.
    simpl_sep_liftn_in Hs 10.    
    eauto.
  }
  { 
    eapply st_rule_reg.
    simpl.
    rewrite in_range44; eauto.
    rewrite H0; eauto.
    rewrite Int.add_assoc.
    eauto.
    eauto.
  }
  {  
    introv Hs.
    simpl update_frame.
    unfold stack_frame.
    sep_cancel1 1 1.
    eapply astar_assoc_intro.
    sep_cancel1 9 1.
    unfold stack_seg.
    asrt_to_line 7. 
    sep_cancel1 1 4. 
    eauto.
  }
Qed.

Lemma st_rule_save_stk_i4 :
  forall grst p l fm1 fm2 v1,
    get_genreg_val grst i4 = v1 ->
    get_genreg_val grst sp = l ->
    |- {{ GenRegs grst ** stack_frame l fm1 fm2 ** p }}
        st i4 (Aro sp (' 48))
      {{ GenRegs grst ** stack_frame l fm1 (update_frame fm2 4 v1) ** p }}.
Proof.
  intros.
  destruct fm1, fm2.
  eapply ins_conseq_rule.
  {
    introv Hs.
    simpl_sep_liftn_in Hs 2.
    unfold stack_frame in Hs.
    eapply astar_assoc_elim in Hs.
    simpl_sep_liftn_in Hs 2.
    unfold stack_seg at 1 in Hs.
    asrt_to_line_in Hs 7.
    simpl_sep_liftn_in Hs 5.
    simpl_sep_liftn_in Hs 10.    
    eauto.
  }
  { 
    eapply st_rule_reg.
    simpl. 
    rewrite in_range48; eauto.
    rewrite H0; eauto.
    rewrite Int.add_assoc.
    eauto.
    eauto.
  }
  {  
    introv Hs.
    simpl update_frame.
    unfold stack_frame.
    sep_cancel1 1 1.
    eapply astar_assoc_intro.
    sep_cancel1 9 1.
    unfold stack_seg.
    asrt_to_line 7. 
    sep_cancel1 1 5. 
    eauto.
  }
Qed.

Lemma st_rule_save_stk_i5 :
  forall grst p l fm1 fm2 v1,
    get_genreg_val grst i5 = v1 ->
    get_genreg_val grst sp = l ->
    |- {{ GenRegs grst ** stack_frame l fm1 fm2 ** p }}
        st i5 (Aro sp (' 52))
      {{ GenRegs grst ** stack_frame l fm1 (update_frame fm2 5 v1) ** p }}.
Proof.
  intros.
  destruct fm1, fm2.
  eapply ins_conseq_rule.
  {
    introv Hs.
    simpl_sep_liftn_in Hs 2.
    unfold stack_frame in Hs.
    eapply astar_assoc_elim in Hs.
    simpl_sep_liftn_in Hs 2.
    unfold stack_seg at 1 in Hs.
    asrt_to_line_in Hs 7.
    simpl_sep_liftn_in Hs 6.
    simpl_sep_liftn_in Hs 10.    
    eauto.
  }
  { 
    eapply st_rule_reg.
    simpl. 
    rewrite in_range52; eauto.
    rewrite H0; eauto.
    rewrite Int.add_assoc.
    eauto.
    eauto.
  }
  {  
    introv Hs.
    simpl update_frame.
    unfold stack_frame.
    sep_cancel1 1 1.
    eapply astar_assoc_intro.
    sep_cancel1 9 1.
    unfold stack_seg.
    asrt_to_line 7. 
    sep_cancel1 1 6. 
    eauto.
  }
Qed.

Lemma st_rule_save_stk_i6 :
  forall grst p l fm1 fm2 v1,
    get_genreg_val grst i6 = v1 ->
    get_genreg_val grst sp = l ->
    |- {{ GenRegs grst ** stack_frame l fm1 fm2 ** p }}
        st i6 (Aro sp (' 56))
      {{ GenRegs grst ** stack_frame l fm1 (update_frame fm2 6 v1) ** p }}.
Proof.
  intros.
  destruct fm1, fm2.
  eapply ins_conseq_rule.
  {
    introv Hs.
    simpl_sep_liftn_in Hs 2.
    unfold stack_frame in Hs.
    eapply astar_assoc_elim in Hs.
    simpl_sep_liftn_in Hs 2.
    unfold stack_seg at 1 in Hs.
    asrt_to_line_in Hs 7.
    simpl_sep_liftn_in Hs 7.
    simpl_sep_liftn_in Hs 10.    
    eauto.
  }
  { 
    eapply st_rule_reg.
    simpl. 
    rewrite in_range56; eauto.
    rewrite H0; eauto.
    rewrite Int.add_assoc.
    eauto.
    eauto.
  }
  {  
    introv Hs.
    simpl update_frame.
    unfold stack_frame.
    sep_cancel1 1 1.
    eapply astar_assoc_intro.
    sep_cancel1 9 1.
    unfold stack_seg.
    asrt_to_line 7. 
    sep_cancel1 1 7. 
    eauto.
  }
Qed.

Lemma st_rule_save_stk_i7 :
  forall grst p l fm1 fm2 v1,
    get_genreg_val grst i7 = v1 ->
    get_genreg_val grst sp = l ->
    |- {{ GenRegs grst ** stack_frame l fm1 fm2 ** p }}
        st i7 (Aro sp (' 60))
      {{ GenRegs grst ** stack_frame l fm1 (update_frame fm2 7 v1) ** p }}.
Proof.
  intros.
  destruct fm1, fm2.
  eapply ins_conseq_rule.
  {
    introv Hs.
    simpl_sep_liftn_in Hs 2.
    unfold stack_frame in Hs.
    eapply astar_assoc_elim in Hs.
    simpl_sep_liftn_in Hs 2.
    unfold stack_seg at 1 in Hs.
    asrt_to_line_in Hs 7.
    simpl_sep_liftn_in Hs 8.
    simpl_sep_liftn_in Hs 10.    
    eauto.
  }
  { 
    eapply st_rule_reg.
    simpl. 
    rewrite in_range60; eauto.
    rewrite H0; eauto.
    rewrite Int.add_assoc.
    eauto.
    eauto.
  }
  {  
    introv Hs.
    simpl update_frame.
    unfold stack_frame.
    sep_cancel1 1 1.
    eapply astar_assoc_intro.
    sep_cancel1 9 1.
    unfold stack_seg.
    asrt_to_line 7. 
    sep_cancel1 1 8. 
    eauto.
  }
Qed.
  
(*+ Lemmas for stack frame constraint +*)
Lemma stack_frame_constraint_pt_same_equal :
  forall fm1 fm2 fm1' fm2' F id vi stk,
    get_frame_nth fm2 6 = get_frame_nth fm2' 6 ->
    stack_frame_constraint stk (fm1 :: fm2 :: F) id vi ->
    stack_frame_constraint stk (fm1' :: fm2' :: F) id vi.
Proof.
  intros.
  unfolds stack_frame_constraint.
  inversion H0; subst.
  {
    eapply frame_invalid; eauto.
  }
  {
    eapply frame_valid; eauto.
    rewrite <- H; eauto.
  }
Qed.

Lemma stk_bottom_pre_pt :
  forall l id F fm1 fm2 fm3 l' lfp s p,
    length F = 13 -> $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 ->
    stack_frame_constraint' l id (F ++ fm1 :: fm2 :: fm3 :: nil) lfp id ->
    get_frame_nth fm1 6 = Some l' -> s |= stack' l lfp ** p ->
    s |= EX lfp1 lfp2 fm' fm'', stack' l lfp1 ** stack_frame l' fm' fm''
         ** stack' (l' -ᵢ ($ 64)) lfp2 ** [| length lfp1 = 6 /\ l' = l -ᵢ ($ (64 * 6)) |] ** p.
Proof.  
  intros.
  do 14 (try destruct F; simpl in H; tryfalse).
  simpl in H1.
  inversion H1; subst.
  {
    eapply post_1_neq in H4; eauto.
    tryfalse.
  }

  inversion H13; subst.
  {
    eapply post_2_neq in H4; tryfalse; eauto.
  }

  clear H1 H9 H13 H10.
  inversion H16; subst.
  {
    eapply post_3_neq in H1; eauto; tryfalse.
  }

  clear H12 H15 H16 H8 H11.
  inversion H13; subst.
  {
    eapply post_4_neq in H1; eauto; tryfalse.
  }

  clear H13 H8 H11.
  inversion H12; subst.
  {
    eapply post_5_neq in H1; eauto; tryfalse.
  }

  clear H12 H8 H11.
  inversion H13; subst.
  {
    eapply post_6_neq in H1; eauto; tryfalse.
  }

  clear H13 H8 H11.
  inversion H12; subst.
  {
    eapply post_7_eq in H1; eauto; tryfalse.
  }
  
  clear H12 H8.
  inversion H13; subst. 
  sep_ex_intro.
  instantiate
    (5 := (fml', fmi')
             :: (fml'0, fmi'0)
                :: (fml'1, fmi'1)
                :: (fml'2, fmi'2) :: (fml'3, fmi'3) :: (fml'4, fmi'4) :: nil).
  instantiate (3 := fml'5).
  instantiate (2 := fmi'5).
  instantiate (1 := lfp0).  
  clear - H3 H11 H2.
  unfolds stack'. folds stack'.
  do 6 (
       match goal with
       | H :  _ |= _ |- _ =>
         eapply astar_assoc_elim in H
       end;
       eapply astar_assoc_intro; sep_cancel1 1 1).
  rewrite H2 in H11.
  inversion H11; subst.
  eapply astar_assoc_elim in H0.
  sep_cancel1 1 2.
  sep_cancel1 1 2.
  simpl_sep_liftn 2.
  eapply sep_pure_l_intro; eauto.
  split; simpl; eauto.
  repeat (rewrite Int.sub_add_opp; eauto).
  repeat (rewrite Int.add_assoc; eauto).
  eapply astar_emp_intro_l; eauto.
  eapply post_8_eq in H0.
  eapply H8 in H0.
  tryfalse.
Qed.

(*+ Lemmas for Space +*)
Lemma stack_frame_combine :
  forall l fm1 fm2 lfp s p,
    s |= stack_frame l fm1 fm2 ** stack' (l -ᵢ ($ 64)) lfp ** p ->
    s |= stack' l ((fm1, fm2) :: lfp) ** p.
Proof.
  intros.
  unfold stack'; fold stack'.
  eapply astar_assoc_intro; eauto.
Qed.