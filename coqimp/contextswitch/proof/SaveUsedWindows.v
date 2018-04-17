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
Lemma neq_rev_still :
  forall {A : Type} (a b : A),
    a <> b ->
    b <> a.
Proof.
  intros.
  intro.
  symmetry in H0.
  tryfalse.
Qed.

Lemma rotate_hold_post_id_neq_oid :
  forall oid id vi i,
    $ 0 <=ᵤᵢ oid <=ᵤᵢ $ 7 -> $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 -> $ 0 <=ᵤᵢ vi <=ᵤᵢ $ 7 ->
    rotate oid id vi i -> post_cwp id <> vi ->
    post_cwp id <> oid.
Proof.
  intros.
  inversion H2; subst.
  eapply post_1_neq; eauto.

  inversion H4; subst.
  eapply post_2_neq; eauto.

  inversion H7; subst.
  eapply post_3_neq; eauto.

  inversion H10; subst.
  eapply post_4_neq; eauto.

  inversion H13; subst.
  eapply post_5_neq; eauto.

  clear H2 H4 H7 H10 H13.
  inversion H16; subst.
  eapply post_6_neq; eauto.

  inversion H2; subst.
  eapply post_7_eq; eauto.

  inversion H10; subst.
  { 
    clear - H H1 H13 H4 H17 H14 H11 H8 H5 H3.
    eapply post_cwp_step_limit_8 with (id := id0) (vi := vi) in H; eauto.
    do 7 (destruct H as [a | H]; [subst; tryfalse | idtac]).
    subst; tryfalse.
  }
  { 
    intro.  
    clear - H1 H22 H13 H4 H17 H14 H11 H8 H5 H3 H21.
    eapply post_cwp_step_limit_8 with (id := id) (vi := vi) in H1; eauto.
    do 7 (destruct H1 as [a | H1]; [subst; tryfalse | idtac]).
    subst; tryfalse.
  }
Qed.

(*+ Lemma for stack frame relation +*)

Lemma stack_frame_match_fm_save :
  forall fm F oid id cl clfp1 clfp2 cstk,
    $ 0 <=ᵤᵢ oid <=ᵤᵢ $ 7 -> $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 -> ostk_lfp_rl cstk cl clfp1 clfp2 ->
    stack_frame_match oid clfp1 (F ++ fm :: nil) id -> length F = 13 ->
    stack_frame_save (F ++ fm :: nil) (cl, clfp1 ++ clfp2)
                     cstk oid (post_cwp id).
Proof.
  intros.
  destruct cstk.
  unfolds ostk_lfp_rl.
  simpljoin1.
  unfold stack_frame_save.
  split; eauto.
  do 14 (try destruct F; simpl in H3; tryfalse).
  simpl in H2.
  
  inversion H2; subst.
  {
    destruct x; tryfalse.
    simpl.
    eapply frame_save_end; eauto.
  }

  destruct x; tryfalse.
  destruct p.
  inversion H11; subst.
  {
    simpl. 
    eapply frame_save_cons; eauto.
    eapply post_cons_neq_still; eauto.
    destruct x; simpl in H4; tryfalse.
    simpl.
    eapply frame_save_end; eauto.
  }

  destruct x; simpl in H4; tryfalse.
  destruct p.
  inversion H13; subst.
  {
    destruct x; simpl in H4; tryfalse.
    simpl.
    do 2 (eapply frame_save_cons; [solve_post_neq | idtac]).
    eapply frame_save_end; eauto.
  }

  destruct x; simpl in H4; tryfalse.
  destruct p.
  inversion H15; subst.
  {
    simpl.
    do 2 (eapply frame_save_cons; [solve_post_neq | idtac]).
    eapply post_cons_neq_still_rev; eauto.
    eapply frame_save_cons; [solve_post_neq | idtac].
    destruct x; simpl in H4; tryfalse.
    simpl.
    eapply frame_save_end; eauto.
  }

  destruct x; simpl in H4; tryfalse.
  destruct p.
  inversion H17; subst.
  {
    simpl.
    destruct x; simpl in H4; tryfalse.
    do 3 (eapply frame_save_cons; [solve_post_neq | idtac];
          try eapply post_cons_neq_still_rev; eauto).
    eapply post_cons_neq_still_rev; eauto.
    eapply frame_save_cons; [solve_post_neq | idtac].
    eapply frame_save_end; eauto.
  }

  destruct x; simpl in H4; tryfalse.
  destruct p.
  inversion H19; subst.
  {
    destruct x; simpl in H4; tryfalse.
    do 4 (eapply frame_save_cons; [solve_post_neq | idtac];
          do 2 (try eapply post_cons_neq_still_rev; eauto)).
    eapply post_cons_neq_still_rev; eauto.
    eapply frame_save_cons; [solve_post_neq | idtac];
      do 2 (try eapply post_cons_neq_still_rev; eauto).
    eapply frame_save_end; eauto.
  }

  destruct x; simpl in H4; tryfalse.
  destruct p.
  inversion H21; subst.
  {
    destruct x; simpl in H4; tryfalse.
    simpl.
    do 6 (try eapply frame_save_cons; [solve_post_neq | idtac];
          repeat (eapply post_cons_neq_still_rev; eauto)).
    eapply frame_save_end; eauto.
  }

  destruct x; simpl in H4; tryfalse.
  destruct p.
  inversion H23; subst.
  {
    destruct x; simpl in H4; tryfalse.
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

Inductive frame_restore1 : Word -> FrameList -> Word -> FrameList -> Prop :=
| restore_end1 : forall F id, frame_restore1 id F id F
| restore_cons1 :
    forall F F' id vi fm1 fm2,
      id <> vi ->
      $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 -> frame_restore1 (post_cwp id) (F' ++ fm1 :: fm2 :: nil) vi F -> 
      frame_restore1 id (fm1 :: fm2 :: F') vi F.

Lemma frame_restore_restore1_eq :
  forall F F' id vi,
    length F = 16 -> length F' = 16 ->
    $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 -> $ 0 <=ᵤᵢ vi <=ᵤᵢ $ 7 ->
    frame_restore id F vi F' ->
    frame_restore1 id F vi F'.
Proof.
  intros.
  do 17 (try destruct F; simpl in H; tryfalse).
  do 17 (try destruct F'; simpl in H0; tryfalse).
  clear H H0.

  (** step0 *)
  inversion H3; subst.
  {
    eapply restore_end1; eauto.
  }

  (** step1 *)
  clear H3.
  assert (length F' = 14).
  {
    assert (length (F' ++ fm1 :: fm2 :: nil) = 16).
    rewrite H; simpl; eauto.
    rewrite app_length in H3.
    simpls; omega.
  }
  do 15 (try destruct F'; simpl in H3; tryfalse).
  simpl in H.
  inversion H; subst.
  clear H H3.
  inversion H8; subst.
  {
    simpl.
    eapply restore_cons1; eauto.
    eapply restore_end1; eauto.
  }

  (** step2 *)
  clear H8.
  assert (length F' = 14).
  {
    assert (length (F' ++ fm1 :: fm2 :: nil) = 16).
    rewrite H; simpl; eauto.
    rewrite app_length in H6.
    simpls; omega.
  }
  do 15 (try destruct F'; simpl in H6; tryfalse).
  simpl in H.
  inversion H; subst.
  clear H H6.
  inversion H10; subst.
  {
    do 2 (eapply restore_cons1; try solve_post_neq;
          repeat (eapply post_cons_neq_still_rev; eauto)).
    eapply restore_end1; eauto.
  }

  (** step3 *)
  clear H10.
  assert (length F' = 14).
  {
    assert (length (F' ++ fm1 :: fm2 :: nil) = 16).
    rewrite H; simpl; eauto.
    rewrite app_length in H8.
    simpls; omega.
  }
  do 15 (try destruct F'; simpl in H8; tryfalse).
  simpl in H.
  inversion H; subst.
  clear H H8.
  inversion H12; subst.
  {
    do 3 (eapply restore_cons1; try solve_post_neq;
          repeat (eapply post_cons_neq_still_rev; eauto)).
    eapply restore_end1; eauto.
  }

  (** step4 *)
  clear H12.
  assert (length F' = 14).
  {
    assert (length (F' ++ fm1 :: fm2 :: nil) = 16).
    rewrite H; simpl; eauto.
    rewrite app_length in H10.
    simpls; omega.
  }
  do 15 (try destruct F'; simpl in H10; tryfalse).
  simpl in H.
  inversion H; subst.
  clear H H10.
  inversion H14; subst.
  {
    do 4 (eapply restore_cons1; try solve_post_neq;
          repeat (eapply post_cons_neq_still_rev; eauto)).
    eapply restore_end1; eauto.
  }

  (** step5 *)
  clear H14.
  assert (length F' = 14).
  {
    assert (length (F' ++ fm1 :: fm2 :: nil) = 16).
    rewrite H; simpl; eauto.
    rewrite app_length in H12.
    simpls; omega.
  }
  do 15 (try destruct F'; simpl in H12; tryfalse).
  simpl in H.
  inversion H; subst.
  clear H H12.
  inversion H16; subst.
  {
    do 5 (eapply restore_cons1; try solve_post_neq;
          repeat (eapply post_cons_neq_still_rev; eauto)).
    eapply restore_end1; eauto.
  }

  (** step 6 *)
  clear H16.
  assert (length F' = 14).
  {
    assert (length (F' ++ fm1 :: fm2 :: nil) = 16).
    rewrite H; simpl; eauto.
    rewrite app_length in H14.
    simpls; omega.
  }
  do 15 (try destruct F'; simpl in H14; tryfalse).
  simpl in H.
  inversion H; subst.
  clear H H14.
  inversion H18; subst.
  {
    do 6 (eapply restore_cons1; try solve_post_neq;
          repeat (eapply post_cons_neq_still_rev; eauto)).
    eapply restore_end1; eauto.
  }

  (** step 7 *)
  clear H18.
  assert (length F' = 14).
  {
    assert (length (F' ++ fm1 :: fm2 :: nil) = 16).
    rewrite H; simpl; eauto.
    rewrite app_length in H16.
    simpls; omega.
  }
  do 15 (try destruct F'; simpl in H16; tryfalse).
  simpl in H.
  inversion H; subst.
  clear H H16.
  inversion H20; subst.
  {
    do 7 (eapply restore_cons1; try solve_post_neq;
          repeat (eapply post_cons_neq_still_rev; eauto)).
    eapply restore_end1; eauto.
  }

  (** step 8 *)
  clear H20.
  assert (length F' = 14).
  {
    assert (length (F' ++ fm1 :: fm2 :: nil) = 16).
    rewrite H; simpl; eauto.
    rewrite app_length in H18.
    simpls; omega.
  }
  do 15 (try destruct F'; simpl in H18; tryfalse).
  simpl in H.
  inversion H; subst.
  clear H H18.
  inversion H22; subst.
  {
    clear - H0 H1.
    rewrite post_8_eq in H0; tryfalse.
    eauto.
  }
  clear - H1 H19 H18 H16 H14 H12 H10 H8 H6 H3.
  eapply post_cwp_step_limit_8 in H1; eauto.
  do 7 (destruct H1 as [a | H1]; [subst; tryfalse | idtac]).
  subst; tryfalse.
Qed.

Ltac post_nth_neq :=
  eapply neq_rev_still; try eapply post_1_neq; try eapply post_2_neq;
  try eapply post_3_neq; try eapply post_4_neq; try eapply post_5_neq;
  try eapply post_6_neq; try eapply post_7_eq; solve_post_inrange.

Lemma stk_fm_match_cons_tail_stable :
  forall F F' oid id lfp fmo fmo' fml fml' fmi fmi' fm1 fm2,
    post_cwp id <> oid -> $ 0 <=ᵤᵢ oid <=ᵤᵢ $ 7 -> $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 ->
    length F = 13 -> length F' = 11 ->
    stack_frame_match oid lfp (F ++ fmo :: nil) id ->
    frame_restore oid (fmo :: fml :: fmi :: F) id
                  (fmo' :: fml' :: fmi' :: fm1 :: fm2 :: F') ->
    stack_frame_match oid (lfp ++ (fm1, fm2) :: nil) (F ++ fmo :: nil) (post_cwp id).
Proof.
  introv Hpost_cwp_neq.
  intros.
  do 14 (destruct F; simpl in H1; tryfalse).
  do 12 (destruct F'; simpl in H2; tryfalse).
  clear H1 H2.

  simpl in H3.
  eapply frame_restore_restore1_eq in H4; eauto.

  (** step0 *)
  inversion H3; subst.
  {
    inversion H4; subst; tryfalse.
    simpl.
    eapply match_cons; eauto; try solve_post_neq.
    eapply match_end; eauto.
  }

  (** step1 *)
  clear H3.
  inversion H4; subst; tryfalse.
  clear H4.
  inversion H10; subst.
  {
    inversion H12; subst; tryfalse.
    simpl.
    do 2 (eapply match_cons; eauto; try post_nth_neq).
    eapply match_end; eauto.
  }

  (** step2 *)
  clear H10.
  inversion H12; subst; tryfalse.
  clear H12.
  inversion H13; subst.
  {
    simpl in H15.
    inversion H15; subst; tryfalse.
    simpl.
    do 3 (eapply match_cons; eauto; try post_nth_neq).
    eapply match_end; eauto.
  }

  (** step3 *)
  clear H13.
  inversion H15; subst; tryfalse.
  clear H15.
  inversion H16; subst.
  {
    simpl in H18.
    inversion H18; subst; tryfalse.
    simpl.
    do 4 (eapply match_cons; eauto; try post_nth_neq).
    eapply match_end; eauto.
  }

  (** step4 *)
  clear H16.
  inversion H18; subst; tryfalse.
  clear H18.
  inversion H19; subst.
  {
    simpl in H21.
    inversion H21; subst; tryfalse.
    simpl.
    do 5 (eapply match_cons; eauto; try post_nth_neq).
    eapply match_end; eauto.
  }

  (** step5 *)
  clear H19.
  inversion H21; subst; tryfalse.
  clear H21.
  inversion H22; subst.
  {
    simpl in H24.
    inversion H24; subst; tryfalse.
    simpl.
    do 6 (eapply match_cons; eauto; try post_nth_neq).
    eapply match_end; eauto.
  }

  (** step6 *)
  clear H22.
  inversion H24; subst; tryfalse.
  clear H24.
  inversion H25; subst.
  {
    simpl in H27.
    inversion H27; subst; tryfalse.
    simpl.
    do 7 (eapply match_cons; eauto; try post_nth_neq).
    eapply match_end; eauto.
  }

  (** step7 *)
  clear H25.
  inversion H27; subst; tryfalse.
  clear H27.  
  inversion H28; subst.
  {
    simpl in H30.
    inversion H30; subst; tryfalse.
    simpl.
    rewrite post_8_eq in Hpost_cwp_neq; eauto.
    tryfalse.
  }
Qed.

Lemma stk_fm_contraint_fm_app_stable :
  forall l id F lfp vi F',
    stack_frame_constraint' l id F lfp vi ->
    stack_frame_constraint' l id (F ++ F') lfp vi.
Proof.
  intros.
  generalize dependent F'.
  induction H; intros.
  -
    eapply frame_invalid; eauto.
  -
    eapply frame_valid; eauto.
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
  renames x'24 to vz, x'25 to vn, x'15 to ct, x'21 to nt, x'13 to ll.
  renames x'16 to cctx, x'20 to cstk, x'17 to cl, x'18 to clfp1, x'19 to clfp2.
  renames x'22 to nctx, x'23 to nstk.
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
    destruct Hctx_win_save as [Hctx_win_save [Hctx_pt_stk Hostk_lfp] ].
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
    clear - Hostk_lfp.
    unfolds ostk_lfp_rl.
    destruct cstk.
    simpljoin1.
    simpls; eauto.
    sep_cancel1 1 1.
    sep_cancel1 1 1.
    eapply sep_pure_l_intro; eauto.
    introv Hct.
    split; eauto.
    split; eauto.
    eapply stack_frame_match_fm_save; eauto.
    simpljoin1; eauto.
    simpljoin1; eauto.
    eapply astar_emp_elim_r; eauto.
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

    assert (Harth : (cl -ᵢ ($ (64 * Z.of_nat (length clfp1)))) -ᵢ ($ 64) =
                      cl -ᵢ ($ (64 * Z.of_nat (length clfp1 + 1)))).
    {
      repeat (rewrite Int.sub_add_opp).
      rewrite Int.add_assoc.
      rewrite <- Int.neg_add_distr.
      assert (Htrivil : ($ (64 * Z.of_nat (length clfp1))) +ᵢ ($ 64) =
                        $ (64 * Z.of_nat (length clfp1 + 1))).
      rewrite Int.add_unsigned.
      assert (Heq64 : Int.unsigned $ 64 = 64%Z).
      eauto.
      rewrite Heq64.
      rewrite Int.unsigned_repr.
      assert (Htrivil_eq : length clfp1 + 1 = S (length clfp1)).
      omega.
      rewrite Htrivil_eq.
      rewrite Nat2Z.inj_succ.
      unfold Z.succ.
      rewrite <- Zred_factor4.
      eauto.
      clear - Hlen_clfp1.
      unfold Int.max_unsigned, Int.modulus, two_power_nat.
      simpl shift_nat.
      omega.
      rewrite Htrivil.
      eauto.
    }
    
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
      eapply stk_fm_match_cons_tail_stable; eauto.
      eapply rotate_hold_post_id_neq_oid; eauto.
      omega.
    }
    
    eapply sep_pure_l_intro.
    {
      instantiate (1 := fmi).
      instantiate (1 := fml).
      do 3 rewrite trivial_assoc_ls.
      eapply restore_cons; eauto.
      eapply rotate_hold_post_id_neq_oid; eauto.
    }

    eapply sep_pure_l_intro.
    {
      rewrite app_length.
      simpl length.
      rewrite Harth in Hstk_fm_constraint1.
      unfold stack_frame_constraint.
      unfold get_stk_addr.
      unfold get_stk_cont.
      remember (cl -ᵢ ($ (64 * Z.of_nat (length clfp1 + 1)))) as offset.
      simpl in Hstk_fm_constraint1.
      do 3 rewrite trivial_assoc_ls.
      assert
        (Htrivial : 
          (([[w44, w45, w46, w47, w48, w49, w50, w51]])
             :: (([[w52, w53, w54, w55, w56, w57, w58, w59]]) :: F') ++
             ([[w7, w8, w9, w10, w11, w12, w13, w14]]) ::
             ([[w15, w16, w17, w18, w19, w20, w21, w22]]) :: nil) =
          (([[w44, w45, w46, w47, w48, w49, w50, w51]])
            :: ([[w52, w53, w54, w55, w56, w57, w58, w59]]) :: F' ++
          ([[w7, w8, w9, w10, w11, w12, w13, w14]]) :: nil) ++
          ([[w15, w16, w17, w18, w19, w20, w21, w22]]) :: nil  
        ).
      rewrite trivial_assoc_ls2.
      eauto.
      rewrite Htrivial.
      rewrite <- app_assoc.
      eapply stk_fm_contraint_fm_app_stable; eauto.
    }

    instantiate (1 := Aemp).
    eapply sep_pure_l_intro; eauto.
    simpl get_frame_nth.
    split; eauto.
    split.
    eapply rotate_cons; eauto.
    split; eauto.
    split.
    eapply g4_rot_stable with (oid := oid); eauto.
    split; eauto.

    eapply sep_pure_l_intro; eauto.
    split; eauto.
    simpljoin1; eauto.
    instantiate (1 := cstk).
    clear - Hctx_win_save.
    destruct Hctx_win_save as [_ Hctx_pt_stk].
    unfolds ctx_pt_stk.
    simpls. 
    destruct Hctx_pt_stk as [ [Hstk_len_gt_zero Hpt] Hostk_lfp_rl ].
    split; eauto.
    try rewrite app_length in *.
    rewrite app_length.
    simpls.
    simpljoin1.
    split; eauto.
    omega.

    clear - Hostk_lfp_rl.
    unfolds ostk_lfp_rl.
    destruct cstk.
    simpljoin1.
    exists (x ++ ([[w3, w6, w29, w31, w32, w33, w34, w35]],
             [[w36, w37, w38, w39, w40, w41, w42, w43]]) :: nil).
    repeat (split; eauto).
    rewrite <- app_assoc.
    simpl; eauto.

    match goal with
    | H : length clfp1 = length _ |- _ =>
      renames H to Hlen_clfp1
    end.
    clear - Hlen_clfp1.
    repeat rewrite app_length.
    simpl.
    rewrite Hlen_clfp1; eauto.

    clear - Hlen_clfp1.
    rewrite app_length.
    simpl.
    assert (Htrivial : length clfp1 + 1 + 0 = S (length clfp1)).
    omega.
    rewrite Htrivial.
    rewrite Nat2Z.inj_succ.
    unfold Z.succ.
    omega.

    rewrite Harth.
    rewrite app_length.
    simpl length.
    assert (Htrivial : length clfp1 + 1 + 0 = length clfp1 + 1).
    eauto.
    rewrite Htrivial.
    eauto.
    omega.
  }
  {
    introv Hs.
    unfold ta0_save_usedwindows_post in Hs.
    sep_ex_elim_in Hs.
    asrt_to_line_in Hs 17.
    sep_ex_intro.
    do 17 sep_cancel1 1 1.
    eapply astar_emp_elim_r; eauto.
  }

  DlyFrameFree_elim.
  eapply in_range_0_7_post_cwp_still; eauto.
  DlyFrameFree_elim.
Qed.