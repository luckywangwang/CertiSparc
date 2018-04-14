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

Lemma in_range_0_7_num :
  forall v,
    $ 0 <=ᵤᵢ v <=ᵤᵢ $ 7 ->
    v = ($ 0) \/ v = ($ 1) \/ v = ($ 2) \/ v = ($ 3) \/
    v = ($ 4) \/ v = ($ 5) \/ v = ($ 6) \/ v = ($ 7).
Proof.
  intros.
  rewrite <- Int.repr_unsigned with (i := v).
  unfolds int_leu.
  unfolds Int.ltu, Int.eq.
  assert (Int.unsigned $ 0 = 0%Z); eauto.
  assert (Int.unsigned $ 7 = 7%Z); eauto.
  try rewrite H0 in *.
  try rewrite H1 in *.
  destruct v.
  simpl Int.unsigned in *.
  destruct (zlt 0 intval); destruct (zeq 0 intval);
    destruct (zlt intval 7); destruct (zeq intval 7); subst; eauto;
      tryfalse; try omega.
  destruct intval; tryfalse; eauto 20.
  do 3 (try destruct p; eauto 10; tryfalse).
  do 7 right.
  eauto.
Qed.

Lemma post_cwp_step_limit_8 :
  forall id vi,
    $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 -> $ 0 <=ᵤᵢ vi <=ᵤᵢ $ 7 ->
    post_cwp id = vi \/ post_cwp (post_cwp id) = vi \/ post_cwp (post_cwp (post_cwp id)) = vi \/
    post_cwp (post_cwp (post_cwp (post_cwp id))) = vi \/
    post_cwp (post_cwp (post_cwp (post_cwp (post_cwp id)))) = vi \/
    post_cwp (post_cwp (post_cwp (post_cwp (post_cwp (post_cwp id))))) = vi \/
    post_cwp (post_cwp (post_cwp (post_cwp (post_cwp (post_cwp (post_cwp id)))))) = vi \/
    post_cwp (post_cwp (post_cwp (post_cwp (post_cwp (post_cwp (post_cwp (post_cwp id))))))) = vi.
Proof.
  intros.
  unfold post_cwp.
  unfold Int.modu.
  unfold Int.add.
  unfold N.
  unfolds int_leu.
  unfolds Int.ltu.
  unfolds Int.eq.
  assert (Int.unsigned $ 0 = 0%Z); eauto.
  assert (Int.unsigned $ 7 = 7%Z); eauto.
  assert (Int.unsigned $ 1 = 1%Z); eauto.
  assert (Int.unsigned $ 8 = 8%Z); eauto.
  try rewrite H1 in *.
  try rewrite H2 in *.
  try rewrite H3 in *.
  try rewrite H4 in *.
  try rewrite <- Int.repr_unsigned with (i := id).
  try rewrite <- Int.repr_unsigned with (i := vi).
  destruct id, vi.
  simpls Int.unsigned.
  destruct (zlt 0 intval); destruct (zeq 0 intval);
    destruct (zlt intval 7); destruct (zeq intval 7);
      destruct (zlt 0 intval0); destruct (zeq 0 intval0);
        destruct (zlt intval0 7); destruct (zeq intval0 7);
          tryfalse; subst; eauto 200; try omega.
  {
    destruct intval, intval0; tryfalse; eauto. 
    do 4 (try destruct p; tryfalse; simpl; eauto 200);
      do 4 (try destruct p0; tryfalse; simpl; eauto 200).
  }
  {
    destruct intval; tryfalse; eauto.
    do 4 (try destruct p; tryfalse; simpl; eauto 200).
  }
  {
    destruct intval; tryfalse; eauto.
    do 4 (try destruct p; tryfalse; simpl; eauto 200).
  }
  {
    destruct intval0; tryfalse; eauto.
    do 4 (try destruct p; tryfalse; simpl; eauto 200).
  }
  {
    destruct intval0; tryfalse; eauto.
    do 4 (try destruct p; tryfalse; simpl; eauto 200).
  }
Qed.
  
(*+ Lemmas for Integer +*)
Lemma in_range_0_7_and_255_stable :
  forall v,
    $ 0 <=ᵤᵢ v <=ᵤᵢ $ 7 ->
    ($ 255) &ᵢ (($ 1) <<ᵢ v) = ($ 1) <<ᵢ v.
Proof.
  intros.
  unfolds int_leu.
  unfolds Int.ltu.
  unfolds Int.eq.
  unfold Int.and.
  unfold Int.shl.
  assert (Int.unsigned $ 0 = 0%Z).
  eauto.
  assert (Int.unsigned $ 1 = 1%Z).
  eauto.
  assert (Int.unsigned $ 7 = 7%Z).
  eauto.
  assert (Int.unsigned $ 255 = 255%Z).
  eauto.
  try rewrite H0 in *.
  try rewrite H1 in *.
  try rewrite H2 in *.
  try rewrite H3 in *.
  destruct v.
  simpl Int.unsigned in *.
  destruct (zlt 0 intval); destruct (zeq 0 intval);
    destruct (zlt intval 7); destruct (zeq intval 7);
      tryfalse; subst; eauto; try omega.
  destruct intval; tryfalse.
  do 3 (destruct p; tryfalse; eauto).
Qed.
  
Lemma in_range_0_7_and :
  forall x v,
    $ 0 <=ᵤᵢ v <=ᵤᵢ $ 7 ->
    x &ᵢ (($ 1) <<ᵢ v) = (get_range 0 7 x) &ᵢ (($ 1) <<ᵢ v).
Proof. 
  intros.
  unfold get_range.
  simpl.
  rewrite Int.shl_zero.
  assert ((($ 1) <<ᵢ ($ 8)) -ᵢ ($ 1) = ($ 255)).
  eauto.
  rewrite H0.
  rewrite Int.and_assoc.
  rewrite in_range_0_7_and_255_stable; eauto.
Qed.

Lemma get_range_0_7_or :
  forall x y,
    get_range 0 7 (x |ᵢ y) = (get_range 0 7 x) |ᵢ (get_range 0 7 y).
Proof. 
  intros.
  unfold get_range.
  simpl.
  rewrite Int.shl_zero.
  assert ((($ 1) <<ᵢ ($ 8)) -ᵢ ($ 1) = ($ 255)).
  eauto.
  rewrite H.
  rewrite Int.and_or_distrib_l; eauto.
Qed.

Inductive rotate : Word -> Word -> Word -> Word -> Prop :=
| rotate_end :
    forall (oid oid vi l : Word),
      rotate oid oid vi (($ 1) <<ᵢ oid)
| rotate_cons :
    forall (oid id vi l : Word),
      rotate oid id vi l -> post_cwp id <> vi -> $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 ->
      rotate oid (post_cwp id) vi ((($ 1) <<ᵢ l |ᵢ l >>ᵢ ($ 7))).

Lemma rotate_no_reach :
  forall oid id vi l,
    $ 0 <=ᵤᵢ oid <=ᵤᵢ $ 7 -> $ 0 <=ᵤᵢ vi <=ᵤᵢ $ 7 -> $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 -> rotate oid id vi l ->
    l <> ($ 15) <<ᵢ ($ 1) |ᵢ ($ 7) <<ᵢ ($ 1).
Proof.
  intros.
  inversion H2; subst.
  {
    intro.
    eapply in_range_0_7_num in H.
    do 7 (destruct H as [a | H]; [subst; tryfalse | idtac]).
    subst; tryfalse.
  }

  inversion H3; subst.
  {
    intro.
    eapply in_range_0_7_num in H.
    do 7 (destruct H as [a | H]; [subst; tryfalse | idtac]).
    subst; tryfalse.
  }
 
  inversion H6; subst.
  { 
    intro.
    eapply in_range_0_7_num in H.
    do 7 (destruct H as [a | H]; [subst; tryfalse | idtac]).
    subst; tryfalse.
  }
 
  inversion H9; subst.
  {
    intro.
    eapply in_range_0_7_num in H.
    do 7 (destruct H as [a | H]; [subst; tryfalse | idtac]).
    subst; tryfalse.
  }

  inversion H12; subst.
  {
    intro.
    eapply in_range_0_7_num in H.
    do 7 (destruct H as [a | H]; [subst; tryfalse | idtac]).
    subst; tryfalse.
  }

  inversion H15; subst.
  {
    intro.
    eapply in_range_0_7_num in H.
    do 7 (destruct H as [a | H]; [subst; tryfalse | idtac]).
    subst; tryfalse.
  }

  inversion H18; subst.
  {
    intro.
    eapply in_range_0_7_num in H.
    do 7 (destruct H as [a | H]; [subst; tryfalse | idtac]).
    subst; tryfalse.
  }

  inversion H21; subst.
  {
    intro.
    eapply in_range_0_7_num in H.
    do 7 (destruct H as [a | H]; [subst; tryfalse | idtac]).
    subst; tryfalse.
  }

  inversion H24; subst.
  {
    intro.
    eapply in_range_0_7_num in H.
    do 7 (destruct H as [a | H]; [subst; tryfalse | idtac]).
    subst; tryfalse.
  }
   
  clear - H29 H0 H22 H16 H10 H16 H7 H19 H13 H20 H25 H28.
  false. 
  eapply post_cwp_step_limit_8 with (vi := vi) in H29; eauto.
  do 7 (destruct H29 as [a | H29]; [tryfalse | idtac]).
  tryfalse.
Qed.
  
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
  renames x'7 to ll, x'9 to ct, x'10 to nt, x'11 to nctx, x'12 to nstk.
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
 
  destruct Hpure as [Hg4 [Hid [Hg4_hid [ Hg7 Hct ] ] ] ].
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

  Lemma tst :
    forall i,
      
  
  rewrite get_range_0_7_or.
  Search Int.shl.
  
    
  >>>>>>>>>>>>>>>>>>