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
Require Import lemmas_ins.

Require Import inssound.

Require Import Coq.Logic.FunctionalExtensionality.
  
Open Scope nat.
Open Scope code_scope.
Open Scope mem_scope.

(*+ Lemmas for Sequence Rule +*)    
Lemma program_step_next :
  forall C S S' pc npc pc' npc',
    P__ C (S, pc, npc) (S', pc', npc') ->
    pc' = npc.
Proof.
  intros.
  inversion H; subst.
  inversion H8; subst; eauto.
Qed.

(*+ Lemmas for Sep Star +*)
Lemma sep_star_subst :
  forall p1 p1' p2 s,
    s |= p1 ** p2 -> p1 ==> p1' ->
    s |= p1' ** p2.
Proof.
  intros.
  sep_star_split_tac.
  simpls.
  simpljoin1.
  eapply H0 in H.
  exists (m, (r, f0), d0) (m0, (r0, f0), d0).
  simpl.
  repeat (split; eauto).
Qed.

(*+ Lemmas for exe-delay +*)
Lemma regz_exe_delay_stable :
  forall D D' (R R' : RegFile) v,
    R z = Some v -> (R', D') = exe_delay R D ->
    R' z = Some v.
Proof.
  intro D.
  induction D; intros.
  -
    simpls.
    inversion H0; subst.
    eauto.
  -
    destruct a, p.
    simpls.
    destruct d.
    {
      destruct (exe_delay R D) eqn:Heqe.
      inversion H0; subst.
      symmetry in Heqe.
      eapply IHD in Heqe; eauto.
      unfold set_R.
      unfold is_indom.
      destruct (r s) eqn : Hr; eauto.
      unfold RegMap.set.
      destruct_rneq.
    }
    {
      destruct (exe_delay R D) eqn:Heqe.
      inversion H0; subst.
      symmetry in Heqe.
      eapply IHD in Heqe; eauto.
    }
Qed.

Lemma regz_exe_delay_stable2 :
  forall D D' (R R' : RegFile) v,
    R' z = Some v -> (R', D') = exe_delay R D ->
    R z = Some v.
Proof.
  intro D.
  induction D; intros.
  -
    simpls.
    inversion H0; subst.
    eauto.

  -
    destruct a, p.
    simpls.
    destruct d.
    {
      destruct (exe_delay R D) eqn:Heqe.
      inversion H0; subst.
      symmetry in Heqe.
      eapply IHD in Heqe; eauto.
      clear - H.
      unfolds set_R.
      unfold is_indom in *.
      destruct (r s) eqn : Heqe; tryfalse; eauto.
      unfolds RegMap.set.
      destruct_rneq_H.
    }
    {
      destruct (exe_delay R D) eqn:Heqe.
      inversion H0; subst.
      symmetry in Heqe.
      eapply IHD in Heqe; eauto.
    }
Qed.

(*+ Lemmas for register state +*)
    
(*+ Lemmas for Safety Instruction Sequence +*)
Lemma safety_ins_seq_post_weak :
  forall I C S pc npc q q' Spec,
    LookupC C pc npc I ->
    safety_insSeq C S pc npc q Spec -> q ==> q' ->
    safety_insSeq C S pc npc q' Spec.
Proof.
  intro I.
  induction I; intros.
  
  - (** i *)
    inversion H; subst.
    renames l to pc.
    inversion H0; get_ins_diff_false.
    eapply i_seq; eauto.
    intros.
    lets Hsafety : H5.
    eapply H4 in Hsafety.
    clear H2 H H3.
    inversion H5; subst.
    inversion H13; get_ins_diff_false; subst.
    clear - IHI H9 Hsafety H1.
    eauto.

  - (** J1 *)
    inversion H; subst.
    renames l to pc, l0 to npc.
    inversion H0; get_ins_diff_false.
    eapply jmpl_seq; eauto.
    intros.
    clear H3 H2.
    lets Hp : H6.
    eapply H4 in Hp; eauto.
    simpljoin1.
    renames x to fp, x1 to L, x0 to fq, x2 to r.
    exists fp fq L r.
    repeat (split; eauto).

  - (** J2 *)
    inversion H; subst.
    renames l to pc, l0 to npc.
    inversion H0; get_ins_diff_false.
    eapply jmpl_seq; eauto.
    intros.
    eapply H4 in H6; eauto.
    simpljoin1.
    renames x to fp, x0 to fq, x1 to L, x2 to r.
    exists fp fq L r.
    repeat (split; eauto).

  - (** call f *)
    inversion H; subst.
    renames l to pc.
    inversion H0; get_ins_diff_false.
    eapply call_seq; eauto.
    clear H2 H3.
    intros.
    eapply H4 in H3; eauto.
    simpljoin1.
    renames x to fp, x0 to fq, x2 to r, x1 to L.
    exists fp fq L r.
    repeat (split; eauto).
    intros.
    eapply H10 in H3.
    eapply IHI; eauto.
    clear - H13.
    do 2 rewrite Int.add_assoc in H13.
    simpls; eauto.

  - (** retl *)
    inversion H; subst.
    renames l to pc, l0 to npc.
    inversion H0; get_ins_diff_false.
    eapply ret_seq; eauto.
    clear H2 H3.
    intros.
    eapply H4 in H3; eauto.
    simpljoin1; eauto.
    split; eauto.

  - (** be *) 
    inversion H; subst.
    renames l to pc, l0 to npc.
    inversion H0; get_ins_diff_false.
    eapply be_seq; eauto.
    clear H2 H3.
    intros.
    lets Hp : H3.
    eapply H4 in H3; eauto.
    simpljoin1.
    exists x.
    repeat (split; eauto).
    intros.
    eapply H5 in H7.
    simpljoin1.
    do 4 eexists.
    repeat (split; eauto).
    intros.
    lets Hfalse : H7.
    eapply H6 in Hfalse.
    inversion H2; subst.
    inversion H19; get_ins_diff_false.
    simpl in H3.
    rewrite get_R_rn_neq_r0 in H3; eauto.
    rewrite get_R_rn_neq_r0 in H26; eauto.
    eapply regz_exe_delay_stable in H3; eauto.
    rewrite H26 in H3.
    inversion H3; subst.
    tryfalse.
    intro; tryfalse.
    intro; tryfalse.
    inversion Hp; subst.
    inversion H24; get_ins_diff_false.
    eapply IHI; eauto. 
    clear - H12.
    rewrite Int.add_assoc.
    eauto.

  - (** bne *)
    inversion H; subst.
    renames l to pc, l0 to npc.
    inversion H0; get_ins_diff_false.
    eapply bne_seq; eauto.
    clear H2 H3.
    intros.
    lets Hp : H3.
    eapply H4 in H3; eauto.
    simpljoin1.
    exists x.
    repeat (split; eauto).
    intros.
    eapply H5 in H7.
    simpljoin1.
    renames x0 to fp, x1 to fq, x2 to L, x3 to r.
    exists fp fq L r.
    repeat (split; eauto).
    intros.
    lets Hfalse : H7.
    eapply H6 in H7.
    inversion H2; subst.
    inversion H19; get_ins_diff_false.
    simpl in H3. 
    rewrite get_R_rn_neq_r0 in H3; eauto.
    rewrite get_R_rn_neq_r0 in H27; eauto.
    eapply regz_exe_delay_stable in H3; eauto.
    rewrite H27 in H3.
    inversion H3; subst.
    tryfalse.
    intro; tryfalse.
    intro; tryfalse.
    inversion Hp; subst.
    inversion H25; get_ins_diff_false.
    eapply IHI; eauto.
    clear - H12.
    rewrite Int.add_assoc.
    eauto.
Qed.

Lemma safety_ins_seq_frame_property :
  forall I C pc npc q r Spec m0 m1 r0 r1 f0 d0,
    LookupC C pc npc I -> (m0, (r0, f0), d0) |= r -> DlyFrameFree r ->
    disjoint m1 m0 -> disjoint r1 r0 -> safety_insSeq C (m1, (r1, f0), d0) pc npc q Spec ->
    safety_insSeq C (merge m1 m0, (merge r1 r0, f0), d0) pc npc (q ** r) Spec.
Proof.
  intro I.
  induction I; intros.

  - (** i *)
    inversion H; subst.
    renames l to pc.
    inversion H4; get_ins_diff_false.
    eapply i_seq; eauto.
    {
      simpljoin1.
      destruct_state x.
      eapply program_step_safety_property with (s := (m1 ⊎ m0, (r1 ⊎ r0, f0), d0))
        in H6; eauto.
      simpljoin1.
      eauto.
      simpl; eauto.
    }
    {
      simpljoin1.
      lets Hsafety : H6.
      eapply H7 in Hsafety.
      destruct_state x.
      clear H7.
      eapply program_step_safety_property with (s := (m1 ⊎ m0, (r1 ⊎ r0, f0), d0))
        in H6; eauto.
      simpljoin1.
      destruct_state x2.
      simpl in H6.
      simpljoin1.
      intros.
      eapply program_step_deterministic in H5; eauto.
      simpljoin1.
      eapply IHI; eauto.
      inversion H9; subst.
      inversion H25; get_ins_diff_false.
      eauto.
      simpl; eauto.
    }

  - (** J1 *)
    inversion H; subst.
    renames l to pc, l0 to npc.
    inversion H4; get_ins_diff_false.
    eapply jmpl_seq; eauto. 
    simpljoin1.
    {
      destruct_state x.
      eapply program_step_safety_property with (s := (m1 ⊎ m0, (r1 ⊎ r0, f0), d0)) in H6; eauto.
      simpljoin1.
      destruct_state x5.
      simpl in H6.
      simpljoin1.
      eapply program_step_safety_property with (s := (m ⊎ m2, (r2 ⊎ r3, f1), d1)) in H8; eauto.
      simpljoin1.
      do 6 eexists.
      eauto.
      simpl; eauto.
      simpl; eauto.
    }
    { 
      intros.
      simpljoin1.
      lets Hp : H6.  
      eapply H7 with (S1 := x) in Hp; eauto.
      simpljoin1.
      renames x5 to fp, x6 to fq, x7 to L, x8 to r'.
      eapply program_step_safety_property with
      (s := (m1 ⊎ m0, (r1 ⊎ r0, f0), d0)) (r := r) in H6;
        eauto.
      simpljoin1.
      destruct_state x.
      destruct_state x6.
      simpl in H16.
      simpljoin1.
      eapply program_step_safety_property with
      (s := (m ⊎ m2, (r2 ⊎ r3, f1), d1)) (r := r) in H11;
        eauto.
      simpljoin1.
      destruct_state x0.
      destruct_state x5.
      simpl in H19.
      simpljoin1.
      clear H7.
      eapply program_step_deterministic in H6; eauto.
      simpljoin1.
      eapply program_step_deterministic in H11; eauto.
      simpljoin1.
      exists fp fq L (r' ** r).
      eapply disj_sep_star_merge with (p2 := r) in H12; eauto.
      eapply sep_star_assoc2 in H12.
      repeat (split; eauto).
      intros.
      eapply sep_star_assoc in H6.
      eapply sep_star_subst; eauto.
      simpl; eauto.
      simpl; eauto.
    }

  - (** J2 *)
    inversion H; subst.
    renames l to pc, l0 to npc.
    inversion H4; get_ins_diff_false.
    eapply jmpl_seq; eauto.
    simpljoin1.
    {
      clear H7.
      eapply program_step_safety_property with (s := (m1 ⊎ m0, (r1 ⊎ r0, f0), d0)) in H6;
        eauto.
      simpljoin1.
      destruct_state x.
      destruct_state x6.
      simpls.
      simpljoin1.
      eapply program_step_safety_property with (s := (m ⊎ m2, (r2 ⊎ r3, f1), d1)) in H8;
        eauto.
      simpljoin1.
      destruct_state x0.
      destruct_state x5.
      simpls.
      simpljoin1.
      do 6 eexists.
      eauto.
      simpl; eauto.
      simpl; eauto.
    }
    {
      simpljoin1.
      lets Hp : H6. 
      eapply H7 with (S1 := x) in Hp; eauto.
      simpljoin1.
      renames x5 to fp, x6 to fq, x7 to L, x8 to r'.
      clear H7. 
      eapply program_step_safety_property with (s := (m1 ⊎ m0, (r1 ⊎ r0, f0), d0)) (r := r)
        in H6; eauto.
      simpljoin1.
      destruct_state x.
      destruct_state x6.
      simpl in H7.
      simpljoin1. 
      eapply program_step_safety_property with (s := (m ⊎ m2, (r2 ⊎ r3, f1), d1)) (r := r)
        in H8; eauto.
      simpljoin1.
      destruct_state x0.
      destruct_state x5.
      simpl in H16.
      simpljoin1.
      intros.
      eapply program_step_deterministic in H6; eauto.
      simpljoin1.
      eapply program_step_deterministic in H8; eauto.
      simpljoin1.
      exists fp fq L (r' ** r).
      repeat (split; eauto).
      eapply disj_sep_star_merge with (p2 := r) in H9; eauto.
      eapply sep_star_assoc2 in H9; eauto.
      intros.
      eapply sep_star_assoc in H6.
      eapply sep_star_subst; eauto.
      simpl; eauto.
      simpl; eauto.
    }

  - (** call f *)
    inversion H; subst.
    renames l to pc.
    inversion H4; get_ins_diff_false.
    eapply call_seq; eauto.
    {
      clear H7.
      simpljoin1.
      eapply program_step_safety_property with (s := (m1 ⊎ m0, (r1 ⊎ r0, f0), d0)) in H6;
        eauto.
      simpljoin1.
      destruct_state x.
      destruct_state x6.
      simpl in H6.
      simpljoin1.
      eapply program_step_safety_property with (s := (m ⊎ m2, (r2 ⊎ r3, f2), d1)) in H7;
        eauto.
      simpljoin1.
      destruct_state x0.
      destruct_state x5.
      simpls.
      simpljoin1.
      do 6 eexists.
      eauto.
      simpl; eauto.
      simpl; eauto.
    }
    {
      simpljoin1.
      lets Hp : H6.
      eapply H7 with (S1 := x) in Hp; eauto.
      clear H7.
      simpljoin1; eauto.
      renames x5 to fp, x6 to fq, x7 to L, x8 to r'.
      eapply program_step_safety_property with (s := (m1 ⊎ m0, (r1 ⊎ r0, f0), d0)) (r := r)
        in H6; eauto.
      simpljoin1.
      destruct_state x.
      destruct_state x4.
      simpl in H6.
      simpljoin1.
      eapply program_step_safety_property with (s := (m ⊎ m2, (r2 ⊎ r3, f2), d1)) (r := r)
        in H8; eauto.
      simpljoin1.
      destruct_state x0.
      destruct_state x3.
      simpl in H18.
      simpljoin1.
      intros.
      eapply program_step_deterministic in H5; eauto.
      simpljoin1.
      eapply program_step_deterministic in H8; eauto.
      simpljoin1.
      exists fp fq L (r' ** r).
      repeat (split; eauto).
      eapply disj_sep_star_merge with (p2 := r) in H10; eauto.
      eapply sep_star_assoc2; eauto.
      intros.
      eapply sep_star_assoc in H5.
      eapply sep_star_split in H5.
      simpljoin1.
      destruct_state x.
      destruct_state x0.
      simpl in H23.
      simpljoin1.
      eapply H13 in H5.
      eapply IHI; eauto.
      clear - H16.
      do 2 rewrite Int.add_assoc in H16.
      eauto.
      simpl; eauto.
      simpl; eauto.
    }

  - (** retl *)
    inversion H; subst.
    renames l to pc, l0 to npc.
    inversion H4; subst; get_ins_diff_false.
    clear H H5.
    eapply ret_seq; eauto.
    {
      simpljoin1.
      eapply program_step_safety_property with (s := (m1 ⊎ m0, (r1 ⊎ r0, f0), d0))
        in H; eauto.
      simpljoin1.
      destruct_state x.
      destruct_state x6.
      simpl in H6.
      simpljoin1.
      eapply program_step_safety_property with (s := (m ⊎ m2, (r2 ⊎ r3, f1), d1))
        in H5; eauto.
      simpljoin1.
      destruct_state x0.
      destruct_state x5.
      simpl in H11.
      simpljoin1.
      do 6 eexists.
      eauto.
      simpl; eauto.
      simpl; eauto.
    }
    {
      simpljoin1.
      lets Hp : H.
      eapply H7 with (S1 := x) in Hp; eauto.
      simpljoin1.
      clear H7.
      eapply program_step_safety_property with
      (s := (m1 ⊎ m0, (r1 ⊎ r0, f0), d0)) (r := r) in H; eauto.
      simpljoin1.
      destruct_state x.
      destruct_state x4.
      simpl in H7.
      simpljoin1.
      eapply program_step_safety_property with
      (s := (m ⊎ m2, (r2 ⊎ r3, f1), d1)) (r := r) in H5; eauto.
      simpljoin1.
      destruct_state x0.
      destruct_state x3.
      simpl in H13.
      simpljoin1.
      simpls.
      intros.
      eapply program_step_deterministic in H; eauto.
      simpljoin1.
      eapply program_step_deterministic in H5; eauto.
      simpljoin1.
      split; eauto.
      exists (m3, (r4, f2), d2) (m4, (r5, f2), d2).
      simpl.
      repeat (split; eauto).
      exists x5.
      split; eauto.
      simpl.
      eapply get_R_merge_still; eauto.
      simpl; eauto.
      simpl; eauto.
    }

  - (** be f *)
    inversion H; subst.
    renames l to pc, l0 to npc.
    inversion H4; subst; get_ins_diff_false.
    clear H H5.
    eapply be_seq; eauto.
    {
      clear H7.
      simpljoin1.
      eapply program_step_safety_property with (s := (m1 ⊎ m0, (r1 ⊎ r0, f0), d0)) (r := r)
        in H; eauto.
      simpljoin1. 
      destruct_state x.
      destruct_state x6.
      simpls.
      simpljoin1.
      eapply program_step_safety_property with (s := (m ⊎ m2, (r2 ⊎ r3, f2), d1)) (r := r)
        in H5; eauto.
      simpljoin1.
      do 6 eexists.
      eauto.
      simpl; eauto.
      simpl; eauto.
    }
    {
      simpljoin1.
      lets Hp : H.
      eapply H7 with (S1 := x) in H; eauto.
      clear H7.
      simpljoin1.
      simpl in H.
      eapply program_step_safety_property with (s := (m1 ⊎ m0, (r1 ⊎ r0, f0), d0)) (r := r)
        in Hp; eauto.
      simpljoin1.
      destruct_state x.
      destruct_state x7.
      simpl in H9.
      simpljoin1.
      eapply program_step_safety_property with (s := (m ⊎ m2, (r2 ⊎ r3, f2), d1)) (r := r)
        in H5; eauto.
      simpljoin1.
      destruct_state x0.
      destruct_state x6.
      simpl in H13.
      simpljoin1.
      intros.
      eapply program_step_deterministic in H8; eauto.
      simpljoin1.
      eapply program_step_deterministic in H5; eauto.
      simpljoin1. 
      exists x5.
      split; eauto.
      simpl.
      eapply get_R_merge_still; eauto.
      split.
      {
        intros.
        eapply H6 in H5.
        simpljoin1.
        renames x to fp, x0 to fq, x6 to L, x7 to r'.
        exists fp fq L (r' ** r).
        repeat (split; eauto).
        eapply disj_sep_star_merge with (p2 := r) in H8; eauto.
        eapply sep_star_assoc2; eauto.
        intros.
        eapply sep_star_assoc in H22.
        eapply sep_star_subst; eauto.
      }
      {
        intros.
        lets Hfalse : H5.
        eapply H7 in H5.
        eapply IHI; eauto.
        inversion H18; subst.   
        inversion H33; get_ins_diff_false.
        rewrite get_R_rn_neq_r0 in H; eauto.
        rewrite get_R_rn_neq_r0 in H35; eauto.
        eapply regz_exe_delay_stable2 in H35; eauto.
        clear - H H35 H36. 
        unfold merge in *.
        rewrite H in H35; eauto.
        inversion H35; subst.
        tryfalse.
        intro; tryfalse.
        intro; tryfalse.
        inversion H19; subst. 
        inversion H38; get_ins_diff_false.
        clear - H15.
        rewrite Int.add_assoc; eauto.
      }

      simpl; eauto.
      simpl; eauto.
    }

  - (** bne aexp *)
    inversion H; subst.
    renames l to pc, l0 to npc.
    inversion H4; subst; get_ins_diff_false.
    clear H H5.
    eapply bne_seq; eauto.
    {
      clear H7.
      simpljoin1.
      eapply program_step_safety_property with (s := (m1 ⊎ m0, (r1 ⊎ r0, f0), d0)) in H;
        eauto.
      simpljoin1.
      destruct_state x.
      destruct_state x6.
      simpl in H6.
      simpljoin1.
      eapply program_step_safety_property with (s := (m ⊎ m2, (r2 ⊎ r3, f2), d1)) in H5;
        eauto.
      simpljoin1.
      do 6 eexists.
      eauto.
      simpl; eauto.
      simpl; eauto.
    }
    {
      simpljoin1.
      lets Hp : H.
      eapply H7 with (S1 := x) in Hp; eauto.
      clear H7.
      eapply program_step_safety_property with (s := (m1 ⊎ m0, (r1 ⊎ r0, f0), d0)) in H;
        eauto.
      simpljoin1.
      destruct_state x.
      destruct_state x6.
      simpl in H7.
      simpljoin1.
      simpl in H6.
      eapply program_step_safety_property with (s := (m ⊎ m2, (r2 ⊎ r3, f2), d1)) in H5;
        eauto.
      simpljoin1.
      destruct_state x0.
      destruct_state x5.
      simpl in H13.
      simpljoin1.
      intros.
      eapply program_step_deterministic in H; eauto.
      simpljoin1.
      eapply program_step_deterministic in H5; eauto.
      simpljoin1. 
      exists x7.
      repeat (split; eauto).
      simpl.
      eapply get_R_merge_still; eauto.
      intros.
      eapply H9 in H.
      simpljoin1.
      renames x to fp, x0 to fq, x5 to L, x6 to r'.
      exists fp fq L (r' ** r).
      repeat (split; eauto).
      eapply disj_sep_star_merge with (p2 := r) in H5; eauto.
      eapply sep_star_assoc2; eauto.
      intros.
      eapply sep_star_assoc in H22.
      eapply sep_star_subst; eauto.

      intros.
      lets Hfalse : H.
      eapply H10 in H.
      eapply IHI; eauto.
      inversion H18; subst. 
      inversion H33; get_ins_diff_false; subst.
      rewrite get_R_rn_neq_r0 in H6; eauto. 
      rewrite get_R_rn_neq_r0 in H35; eauto.
      eapply regz_exe_delay_stable2 in H35; eauto. 
      unfold merge in H35. 
      rewrite H6 in H35. 
      inversion H35; subst.
      tryfalse.
      intro; tryfalse.
      intro; tryfalse.
      inversion H19; subst.
      inversion H39; get_ins_diff_false.
      clear - H15.
      rewrite Int.add_assoc; eauto.

      simpl; eauto.
      simpl; eauto.
    }
Qed.

Lemma safety_ins_seq_post_disj1 :
  forall I q1 q2 pc npc Spec C S,
    LookupC C pc npc I ->
    safety_insSeq C S pc npc q1 Spec ->
    safety_insSeq C S pc npc (q1 \\// q2) Spec.
Proof.
  intro I.
  induction I; intros.

  - (** i *)
    inversion H; subst.
    renames l to pc.
    inversion H0; get_ins_diff_false.
    clear H1.
    eapply i_seq; eauto.
    intros.
    lets Hq1 : H1.
    eapply H3 in Hq1; eauto.
    inversion H1; subst.
    inversion H14; get_ins_diff_false.
    eauto.

  - (** J1 *)
    inversion H; subst.
    renames l to pc, l0 to npc.
    inversion H0; get_ins_diff_false.
    eapply jmpl_seq; eauto.
    intros.
    lets Hq1 : H4.
    eapply H3 with (S1 := S1) in Hq1; eauto.
    simpljoin1.
    renames x to fp, x0 to fq, x1 to L, x2 to r.
    exists fp fq L r.
    repeat (split; eauto).
    intros.
    eapply H9 in H1; simpl; eauto.

  - (** J2 *)
    inversion H; subst.
    renames l to pc, l0 to npc.
    inversion H0; get_ins_diff_false.
    clear H1.
    eapply jmpl_seq; eauto.
    intros.
    lets Hq1 : H1.
    eapply H3 with (S1 := S1) in Hq1; eauto.
    simpljoin1.
    renames x to fp, x0 to fq, x1 to L, x2 to r.
    exists fp fq L r.
    repeat (split; eauto).
    intros.
    eapply H8 in H12; eauto.
    simpl; eauto.

  - (** call *)
    inversion H; subst.
    renames l to pc.
    inversion H0; get_ins_diff_false.
    eapply call_seq; eauto.
    intros.
    lets Hq1 : H4.
    eapply H3 with (S1 := S1) in Hq1; eauto.
    simpljoin1.
    renames x to fp, x0 to fq, x1 to L, x2 to r.
    exists fp fq L r.
    repeat (split; eauto).
    intros.
    eapply H14 in H1; eauto.
    eapply IHI; eauto.
    clear - H12.
    do 2 rewrite Int.add_assoc in H12; eauto.

  - (** retl *)
    inversion H; subst.
    renames l to pc, l0 to npc.
    inversion H0; get_ins_diff_false.
    eapply ret_seq; eauto.
    intros.
    lets Hq1 : H4.
    eapply H3 with (S1 := S1) in Hq1; eauto.
    simpljoin1.
    split; simpl; eauto.

  - (** be *)
    inversion H; subst.
    renames l to pc, l0 to npc.
    inversion H0; get_ins_diff_false.
    eapply be_seq; eauto.
    intros.
    lets Hq1 : H4.
    eapply H3 with (S1 := S1) in Hq1; eauto.
    simpljoin1.
    exists x.
    repeat (split; eauto).
    intro.
    eapply H8 in H1.
    simpljoin1.
    exists x6 x7 x8 x9.
    repeat (split; eauto).
    intros.
    simpl; eauto.
    intro.
    lets Hx : H1.
    eapply H9 in H1.
    eapply IHI; eauto.
    inversion H4; subst. 
    inversion H21; get_ins_diff_false.
    simpl in H6.
    rewrite get_R_rn_neq_r0 in H6; eauto.
    rewrite get_R_rn_neq_r0 in H29; eauto.
    eapply regz_exe_delay_stable2 in H29; eauto.
    rewrite H6 in H29.
    inversion H29; subst.
    tryfalse.
    intro; tryfalse.
    intro; tryfalse.
    inversion H5; subst.
    inversion H27; get_ins_diff_false.
    clear - H11.
    rewrite Int.add_assoc; eauto.

  - (** bne *)
    inversion H; subst.
    renames l to pc, l0 to npc.
    inversion H0; get_ins_diff_false.
    eapply bne_seq; eauto.
    intros.
    lets Hq1 : H4.
    eapply H3 with (S1 := S1) in Hq1; eauto.
    simpljoin1.
    exists x.
    repeat (split; eauto).
    intros.
    lets Hx : H1.
    eapply H8 in H1; eauto.
    simpljoin1.
    exists x6 x7 x8 x9.
    repeat (split; eauto).
    intros; simpl; eauto.
    intros.
    lets Hx : H1.
    eapply H9 in H1; eauto.
    eapply IHI; eauto.
    inversion H4; subst.
    inversion H21; get_ins_diff_false.
    simpl in H6.
    rewrite get_R_rn_neq_r0 in H6; eauto.
    rewrite get_R_rn_neq_r0 in H29; eauto.
    eapply regz_exe_delay_stable2 in H29; eauto.
    rewrite H6 in H29.
    inversion H29; subst.
    tryfalse.
    intro; tryfalse.
    intro; tryfalse.
    inversion H5; subst.
    inversion H27; get_ins_diff_false.
    clear - H11.
    rewrite Int.add_assoc; eauto.
Qed.

Lemma safety_ins_seq_post_disj2 :
  forall I q1 q2 pc npc Spec C S,
    LookupC C pc npc I ->
    safety_insSeq C S pc npc q2 Spec ->
    safety_insSeq C S pc npc (q1 \\// q2) Spec.
Proof.
  intro I.
  induction I; intros.

  - (** i *)
    inversion H; subst.
    renames l to pc.
    inversion H0; get_ins_diff_false.
    clear H1.
    eapply i_seq; eauto.
    intros.
    lets Hq1 : H1.
    eapply H3 in Hq1; eauto.
    inversion H1; subst.
    inversion H14; get_ins_diff_false.
    eauto.

  - (** J1 *)
    inversion H; subst.
    renames l to pc, l0 to npc.
    inversion H0; get_ins_diff_false.
    eapply jmpl_seq; eauto.
    intros.
    lets Hq1 : H4.
    eapply H3 with (S1 := S1) in Hq1; eauto.
    simpljoin1.
    renames x to fp, x0 to fq, x1 to L, x2 to r.
    exists fp fq L r.
    repeat (split; eauto).
    intros.
    eapply H9 in H1; simpl; eauto.

  - (** J2 *)
    inversion H; subst.
    renames l to pc, l0 to npc.
    inversion H0; get_ins_diff_false.
    clear H1.
    eapply jmpl_seq; eauto.
    intros.
    lets Hq1 : H1.
    eapply H3 with (S1 := S1) in Hq1; eauto.
    simpljoin1.
    renames x to fp, x0 to fq, x1 to L, x2 to r.
    exists fp fq L r.
    repeat (split; eauto).
    intros.
    eapply H8 in H12; eauto.
    simpl; eauto.

  - (** call *)
    inversion H; subst.
    renames l to pc.
    inversion H0; get_ins_diff_false.
    eapply call_seq; eauto.
    intros.
    lets Hq1 : H4.
    eapply H3 with (S1 := S1) in Hq1; eauto.
    simpljoin1.
    renames x to fp, x0 to fq, x1 to L, x2 to r.
    exists fp fq L r.
    repeat (split; eauto).
    intros.
    eapply H14 in H1; eauto.
    eapply IHI; eauto.
    clear - H12.
    do 2 rewrite Int.add_assoc in H12; eauto.

  - (** retl *)
    inversion H; subst.
    renames l to pc, l0 to npc.
    inversion H0; get_ins_diff_false.
    eapply ret_seq; eauto.
    intros.
    lets Hq1 : H4.
    eapply H3 with (S1 := S1) in Hq1; eauto.
    simpljoin1.
    split; simpl; eauto.

  - (** be *)
    inversion H; subst.
    renames l to pc, l0 to npc.
    inversion H0; get_ins_diff_false.
    eapply be_seq; eauto.
    intros.
    lets Hq1 : H4.
    eapply H3 with (S1 := S1) in Hq1; eauto.
    simpljoin1.
    exists x.
    repeat (split; eauto).
    intro.
    eapply H8 in H1.
    simpljoin1.
    exists x6 x7 x8 x9.
    repeat (split; eauto).
    intros.
    simpl; eauto.
    intro.
    lets Hx : H1.
    eapply H9 in H1.
    eapply IHI; eauto.
    inversion H4; subst.
    inversion H21; get_ins_diff_false.
    simpl in H6.
    rewrite get_R_rn_neq_r0 in H6; eauto.
    rewrite get_R_rn_neq_r0 in H29; eauto.
    eapply regz_exe_delay_stable2 in H29; eauto.
    rewrite H6 in H29.
    inversion H29; subst.
    tryfalse.
    intro; tryfalse.
    intro; tryfalse.
    inversion H5; subst.
    inversion H27; get_ins_diff_false.
    clear - H11.
    rewrite Int.add_assoc; eauto.

  - (** bne *)
    inversion H; subst.
    renames l to pc, l0 to npc.
    inversion H0; get_ins_diff_false.
    eapply bne_seq; eauto.
    intros.
    lets Hq1 : H4.
    eapply H3 with (S1 := S1) in Hq1; eauto.
    simpljoin1.
    exists x.
    repeat (split; eauto).
    intros.
    lets Hx : H1.
    eapply H8 in H1; eauto.
    simpljoin1.
    exists x6 x7 x8 x9.
    repeat (split; eauto).
    intros; simpl; eauto.
    intros.
    lets Hx : H1.
    eapply H9 in H1; eauto.
    eapply IHI; eauto.
    inversion H4; subst.
    inversion H21; get_ins_diff_false.
    simpl in H6.
    rewrite get_R_rn_neq_r0 in H6; eauto.
    rewrite get_R_rn_neq_r0 in H29; eauto.
    eapply regz_exe_delay_stable2 in H29; eauto.
    rewrite H6 in H29.
    inversion H29; subst.
    tryfalse.
    intro; tryfalse.
    intro; tryfalse.
    inversion H5; subst.
    inversion H27; get_ins_diff_false.
    clear - H11.
    rewrite Int.add_assoc; eauto.
Qed.
    
(*+ Instruction Sequence Rule Sound +*)
Theorem wf_seq_seq_rule :
  forall p p' i q f Spec I,
    ins_sound (p ↓) p' i -> insSeq_sound Spec p' I q ->
    insSeq_sound Spec p (f#i;;I) q.
Proof.
  intros.
  unfolds insSeq_sound.
  intros.
  inversion H1; subst.
  unfolds ins_sound.
  eapply i_seq; eauto.

  (** progress *)
  destruct_state S.
  assert (exists R' D', exe_delay r d = (R', D')).
  {    
    eapply exe_delay_no_abort; eauto.
  }
  simpljoin1.
  renames x to R', x0 to D'.
  lets Hexe_delay : H3.
  symmetry in H3.
  eapply dly_reduce_asrt_stable in H3; eauto.
  eapply H in H3; eauto.
  simpljoin1.
  exists x npc (npc +ᵢ ($ 4)).
  destruct_state x.
  econstructor; eauto.
  eapply NTrans; eauto.

  (** preservation *)
  intros.
  inversion H3; subst.
  eapply dly_reduce_asrt_stable in H7; eauto.
  eapply H in H7; eauto.
  simpljoin1.
  inversion H14; get_ins_diff_false.
  eapply ins_exec_deterministic in H4; eauto.
  simpljoin1.
  eapply H0 in H5; eauto.
Qed.

Theorem wf_seq_call_rule :
  forall p q fp fq L f p1 p2 p' v i Spec r I f1 f2,
    Spec (f, f +ᵢ ($ 4)) = Some (fp, fq) ->
    (p ↓) ==> r15 |=> v ** p1 -> ins_sound (r15 |=> f1 ** p1 ↓) p2 i ->
    fp L ==> Or r15 ==ₑ f1 -> p2 ==> fp L ** r ->
    fq L ** r ==> p' -> fq L ==> Or r15 ==ₑ f1 -> DlyFrameFree r ->
    insSeq_sound Spec p' I q ->
    insSeq_sound Spec p (f1 c> call f;; f2 c> i;;I) q.
Proof.
  intros.
  unfold insSeq_sound.
  intros.
  inversion H8; subst.
  eapply call_seq; eauto.

  (** progress *)
  destruct_state S.
  assert (exists R' D', exe_delay r0 d = (R', D')).
  {    
    eapply exe_delay_no_abort; eauto.
  }
  simpljoin1.
  renames x to R', x0 to D'.
  lets Hexe_delay : H10.
  symmetry in Hexe_delay.
  eapply dly_reduce_asrt_stable in Hexe_delay; eauto.
  eapply H0 in Hexe_delay.
  lets Hf : Hexe_delay.
  eapply reg_vl_change with (v1 := f1) in Hf; eauto.
  assert (exists R'' D'', exe_delay (set_R R' r15 f1) D' = (R'', D'')).
  {    
    eapply exe_delay_no_abort; eauto.
  }
  simpljoin1.
  lets Hexe_delay2 : H11.
  renames x to R'', x0 to D''.
  symmetry in H11.
  eapply dly_reduce_asrt_stable in H11; eauto.
  eapply H1 in H11; eauto.
  simpljoin1.
  exists (m, (set_R R' r15 f1, f0), D') x (f1 +ᵢ ($ 4)) f f (f +ᵢ ($ 4)).
  split; eauto.
  econstructor; eauto.
  eapply Call; eauto.
  clear - Hexe_delay.
  sep_star_split_tac.
  simpls.
  simpljoin1.
  unfolds regSt.
  simpls.
  simpljoin1.
  eapply indom_merge_still; eauto.
  eapply regset_l_l_indom; eauto.
  destruct_state x.
  econstructor; eauto.
  eapply NTrans; eauto.

  (** preservation *)
  intros.
  inversion H10; subst.
  inversion H23; get_ins_diff_false.
  clear H18.
  inversion H11; subst. 
  inversion H28; get_ins_diff_false.
  exists fp fq L r.
  repeat (split; eauto).
  eapply dly_reduce_asrt_stable in H15; eauto.
  eapply H0 in H15.
  eapply reg_vl_change with (v1 := f1) in H15; eauto.
  eapply dly_reduce_asrt_stable in H16; eauto.
  eapply H1 in H16.
  simpljoin1.
  eapply ins_exec_deterministic in H26; eauto.
  simpljoin1.
  eauto.
  intros.
  eapply H4 in H12.
  clear - H7 H21 H12.
  unfolds insSeq_sound.
  eapply H7 in H21; eauto.
  do 2 rewrite Int.add_assoc in H21; eauto.
  eapply H2 in H12.
  clear - H12.
  destruct_state S'.
  simpls.
  eauto.
  eapply H5 in H13.
  clear - H13.
  destruct_state S''.
  simpls.
  eauto.
Qed.

Theorem wf_seq_ret_rule :
  forall p p' q i Spec f1 f2,
    ins_sound ((p ↓) ↓) p' i ->
    p' ==> q -> fretSta ((p ↓) ↓) p' ->
    insSeq_sound Spec p (f1 r> retl ;; f2 r> i) q.
Proof.
  intros.
  unfolds insSeq_sound.
  intros.
  inversion H2; subst.
  eapply ret_seq; eauto.

  (** progress *)
  destruct_state S.
  assert (exists R' D', exe_delay r d = (R', D')).
  {
    eapply exe_delay_no_abort; eauto.
  }
  simpljoin1.
  renames x to R', x0 to D'.
  symmetry in H4.
  lets Hexe_delay1 : H4.
  eapply dly_reduce_asrt_stable in Hexe_delay1; eauto.
  assert (exists R'' D'', exe_delay R' D' = (R'', D'')).
  {
    eapply exe_delay_no_abort; eauto.
  }
  simpljoin1.
  renames x to R'', x0 to D''.
  symmetry in H5.
  lets Hexe_delay2 : H5. 
  eapply dly_reduce_asrt_stable in Hexe_delay2; eauto.
  lets Hp' : Hexe_delay2.
  eapply H in Hp'; eauto.
  simpljoin1.
  lets Hret_f : H7.
  eapply H1 in Hret_f; eauto.
  simpljoin1. 
  exists (m, (R', f), D') x f2 (x0 +ᵢ ($ 8)) (x0 +ᵢ ($ 8)) ((x0 +ᵢ ($ 8)) +ᵢ ($ 4)).
  split; eauto.
  econstructor; eauto.
  eapply Retl; eauto.
  simpls. 
  clear - H5 H8.
  unfolds get_R.
  eapply exe_delay_general_reg_stable in H8; eauto.
  rewrite H8; eauto.
  destruct_state x.
  econstructor; eauto.
  eapply NTrans; eauto.

  (** preservation *)
  intros.
  inversion H4; subst.
  inversion H16; get_ins_diff_false.
  clear H12.
  inversion H5; subst.
  inversion H21; get_ins_diff_false.
  lets Hexe_delay1 : H10.
  lets Hexe_delay2 : H12.
  eapply dly_reduce_asrt_stable in H10; eauto.
  eapply dly_reduce_asrt_stable in H12; eauto.
  lets Hp' : H12.
  eapply H in Hp'; eauto.
  simpljoin1. 
  eapply ins_exec_deterministic in H19; eauto.
  subst.
  split; eauto.
  exists f.
  simpl.
  repeat (split; eauto).
  eapply H1 in H7; eauto.
  simpljoin1.
  simpls.
  symmetry in Hexe_delay2.
  rewrite get_R_rn_neq_r0; eauto.
  2 : intro; tryfalse.
  rewrite get_R_rn_neq_r0 in H24; eauto.
  2 : intro; tryfalse.
  eapply exe_delay_general_reg_stable with (r := r15) in Hexe_delay2; eauto.
  eapply Hexe_delay2 in H24.
  rewrite H24 in H7.
  inversion H7; subst.
  eauto.
  rewrite Int.add_assoc; eauto.
Qed.

Theorem wf_seq_j1_rule :
  forall f1 f2 f aexp (r1 : GenReg) i p p' p1 q fp fq r Spec L v,
    Spec (f, f +ᵢ ($ 4)) = Some (fp, fq) ->
    (p ↓) ==> aexp ==ₓ f -> (p ↓) ==> r1 |=> v ** p1 ->
    ins_sound (r1 |=> f1 ** p1 ↓) p' i ->
    p' ==> fp L ** r -> fq L ** r ==> q -> DlyFrameFree r ->
    insSeq_sound Spec p (consJ1 f1 aexp r1 f2 i) q.
Proof.
  intros.
  unfold insSeq_sound.
  intros.
  inversion H6; subst.
  eapply jmpl_seq; eauto.

  (** progress *)
  destruct_state S.
  assert (exists R' D', exe_delay r0 d = (R', D')).
  {
    eapply exe_delay_no_abort; eauto.
  }
  simpljoin1.
  renames x to R', x0 to D'.
  lets Hexe_delay1 : H8.
  symmetry in Hexe_delay1.
  eapply dly_reduce_asrt_stable in Hexe_delay1; eauto.
  lets Haexp : Hexe_delay1.
  lets Hf1 : Hexe_delay1.
  eapply H0 in Haexp.
  eapply H1 in Hf1.
  lets Hf1' : Hf1.
  eapply reg_vl_change with (v1 := f1) in Hf1'; eauto.
  assert (exists R'' D'', exe_delay (set_R R' r1 f1) D' = (R'', D'')).
  {
    eapply exe_delay_no_abort; eauto.
  }
  simpljoin1.
  renames x to R'', x0 to D''.
  lets Hexe_delay2 : H9.
  symmetry in Hexe_delay2.
  eapply dly_reduce_asrt_stable in Hexe_delay2; eauto.
  eapply H2 in Hexe_delay2; eauto.
  simpljoin1. 
  exists (m, (set_R R' r1 f1, f0), D') x f2 f f (f +ᵢ ($ 4)).
  split; eauto.
  econstructor; eauto.
  eapply Jumpl; eauto.
  clear - Haexp.
  simpls; eauto.
  simpljoin1; eauto.
  clear - Haexp.
  simpls.
  simpljoin1; eauto.
  clear - Hf1.
  sep_star_split_tac.
  simpls.
  simpljoin1.
  unfolds regSt.
  simpls.
  simpljoin1.
  eapply indom_merge_still; eauto.
  eapply regset_l_l_indom; eauto.
  destruct_state x.
  econstructor; eauto.
  eapply NTrans; eauto.

  (** preservation *)
  intros.
  inversion H8; subst.
  eapply dly_reduce_asrt_stable in H14; eauto.
  lets Haexp : H14.
  lets Hf1 : H14.
  eapply H0 in Haexp.
  simpl in Haexp.
  simpljoin1.
  inversion H20; get_ins_diff_false.
  rewrite H10 in H30.
  inversion H30; subst.
  clear H30.
  inversion H9; subst. 
  inversion H28; get_ins_diff_false.
  exists fp fq L r.
  repeat (split; eauto).
  eapply H1 in Hf1.
  eapply reg_vl_change with (v1 := f1) in Hf1; eauto.
  eapply dly_reduce_asrt_stable in H18; eauto.
  eapply H2 in H18; eauto.
  simpljoin1.
  eapply ins_exec_deterministic in H26; eauto.
  subst.
  eauto.
Qed.

Theorem wf_seq_J2_rule :
  forall p p1 p2 q f1 f1' f2 f2' aexp1 aexp2 (r1 r2 : GenReg) fp fq L r Spec v1 v2,
    Spec (f1', f2') = Some (fp, fq) ->
    (p ↓) ==> aexp1 ==ₓ f1' -> (p ↓) ==> r1 |=> v1 ** p1 ->
    (r1 |=> f1 ** p1 ↓) ==> aexp2 ==ₓ f2' -> (r1 |=> f1 ** p1 ↓) ==> r2 |=> v2 ** p2 ->
    r2 |=> f2 ** p2 ==> fp L ** r -> fq L ** r ==> q -> DlyFrameFree r ->
    insSeq_sound Spec p (consJ2 f1 aexp1 r1 f2 aexp2 r2) q.
Proof.
  intros.
  unfold insSeq_sound.
  intros.
  inversion H7; subst.
  eapply jmpl_seq; eauto.

  (** progress *)
  destruct_state S.
  assert (exists R' D', exe_delay r0 d = (R', D')).
  {
    eapply exe_delay_no_abort; eauto.
  }
  simpljoin1.
  renames x to R', x0 to D'.
  lets Hexe_delay1 : H9.
  symmetry in Hexe_delay1.
  eapply dly_reduce_asrt_stable in Hexe_delay1; eauto.
  lets Haexp1 : Hexe_delay1.
  lets Hf1 : Hexe_delay1.
  eapply H0 in Haexp1.
  eapply H1 in Hf1.
  lets Hf1' : Hf1.
  eapply reg_vl_change with (v1 := f1) in Hf1; eauto.
  assert (exists R'' D'', exe_delay (set_R R' r1 f1) D' = (R'', D'')).
  {
    eapply exe_delay_no_abort; eauto.
  }
  simpljoin1.
  renames x to R'', x0 to D''.
  lets Hexe_delay2 : H10.
  symmetry in Hexe_delay2.
  eapply dly_reduce_asrt_stable in Hexe_delay2; eauto.
  lets Haexp2 : Hexe_delay2.
  lets Hf2 : Hexe_delay2.
  eapply H2 in Haexp2; eauto.
  eapply H3 in Hf2; eauto.
  simpl in Haexp1.
  simpl in Haexp2.
  simpljoin1.
  exists (m, (set_R R' r1 f1, f), D') (m, (set_R R'' r2 f2, f), D'') f2 f1' f1' f2'.
  split; eauto.
  econstructor; eauto.
  eapply Jumpl; eauto.
  clear - Hf1'.
  sep_star_split_tac.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  eapply indom_merge_still; eauto.
  eapply regset_l_l_indom; eauto.
  econstructor; eauto.
  eapply Jumpl; eauto.
  clear - Hf2.
  sep_star_split_tac.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  eapply indom_merge_still; eauto.
  eapply regset_l_l_indom; eauto.

  (** preservation *)
  intros.
  inversion H9; subst.
  eapply dly_reduce_asrt_stable in H15; eauto.
  lets Haexp1 : H15.
  lets Hf1 : H15.
  eapply H0 in Haexp1.
  eapply H1 in Hf1.
  inversion H21; get_ins_diff_false.
  simpl in Haexp1.
  simpljoin1.
  rewrite H11 in H29.
  inversion H29; subst.
  clear H29.
  inversion H10; subst.
  lets Hf1' : Hf1.
  eapply reg_vl_change with (v1 := f1) in Hf1'; eauto.
  eapply dly_reduce_asrt_stable in H18; eauto.
  lets Haexp2 : H18.
  lets Hf2 : H18.
  eapply H2 in Haexp2.
  eapply H3 in Hf2.
  simpl in Haexp2.
  simpljoin1.
  inversion H28; get_ins_diff_false.
  rewrite H13 in H37.
  inversion H37; subst.
  exists fp fq L r.
  repeat (split; eauto).
  eapply reg_vl_change with (v1 := pc1) in Hf2; eauto.
Qed.

Lemma wf_seq_be_rule :
  forall p p' q r f1 f2 f i fp fq L I bv Spec,
    Spec (f, f +ᵢ ($ 4)) = Some (fp, fq) -> DlyFrameFree r ->
    (p ↓) ==> z |=> bv ** Atrue ->
    ins_sound ((p ↓) ↓) p' i ->
    (bv =ᵢ ($ 0) = false -> p' ==> fp L ** r /\ fq L ** r ==> q) ->
    (bv =ᵢ ($ 0) = true -> insSeq_sound Spec p' I q) ->
    insSeq_sound Spec p (f1 e> be f;; f2 e> i;;I) q.
Proof. 
  introv H Hr.
  intros.
  unfold insSeq_sound.
  intros.
  inversion H4; subst.
  eapply be_seq; eauto.

  (** progress *)
  destruct_state S.
  assert (exists R' D', exe_delay r0 d = (R', D')).
  {
    eapply exe_delay_no_abort; eauto.
  }
  simpljoin1.
  renames x to R', x0 to D'.
  lets Hp : H6.
  symmetry in Hp.
  eapply dly_reduce_asrt_stable in Hp; eauto.
  assert (exists R'' D'', exe_delay R' D' = (R'', D'')).
  {
    eapply exe_delay_no_abort; eauto.
  }
  simpljoin1.
  renames x to R'', x0 to D''.
  lets Hp' : H7.
  symmetry in Hp'.
  eapply dly_reduce_asrt_stable in Hp'; eauto.
  eapply H1 in Hp'.
  simpljoin1.
  lets Hz : Hp.
  eapply H0 in Hz.
  destruct (Int.eq bv ($ 0)) eqn:Heqe.
  {
    exists (m, (R', f0), D') x f2 (f2 +ᵢ ($ 4)) (f2 +ᵢ ($ 4)) ((f2 +ᵢ ($ 4)) +ᵢ ($ 4)).
    split; eauto.
    econstructor; eauto.
    eapply Be_false with (f := f); eauto.
    clear - Heqe Hz.
    sep_star_split_tac.
    simpls.
    simpljoin1.
    unfolds regSt.
    simpls.
    simpljoin1. 
    eapply int_eq_true_eq in Heqe.
    rewrite get_R_rn_neq_r0; eauto.
    unfold merge.
    subst.
    unfold RegMap.set.
    destruct_rneq; eauto.
    intro; tryfalse.
    destruct_state x.
    econstructor; eauto.
    eapply NTrans; eauto.
  }
  {  
    exists (m, (R', f0), D') x f2 f f (f +ᵢ ($ 4)).
    split; eauto.
    econstructor; eauto.
    eapply Be_true with (v := bv); eauto.
    clear - Hz.
    sep_star_split_tac.
    simpls.
    unfolds regSt.
    simpls.
    simpljoin1.
    rewrite get_R_rn_neq_r0; eauto.
    2 : intro; tryfalse.
    unfold merge.
    unfold RegMap.set.
    destruct_rneq.
    clear - Heqe.
    eapply int_eq_false_neq in Heqe; eauto.
    destruct_state x.
    econstructor; eauto.
    eapply NTrans; eauto.
  }

  (** preservation *)
  intros. 
  inversion H6; subst.
  inversion H7; subst.
  exists bv.
  split; eauto.
  lets Hexe_delay1 : H11.
  eapply dly_reduce_asrt_stable in H11; eauto.
  inversion H19; get_ins_diff_false.
  eapply dly_reduce_asrt_stable in H13; eauto.
  clear H17. 
  eapply H0 in H11.  
  clear - Hexe_delay1 H11 H29.
  sep_star_split_tac.
  simpls. 
  unfolds regSt.
  simpls. 
  simpljoin1.
  rewrite get_R_rn_neq_r0; eauto.
  2 : intro; tryfalse.
  rewrite get_R_rn_neq_r0 in H29; eauto.
  2 : intro; tryfalse.
  lets Hz : H29.
  unfold merge in Hz.
  unfold RegMap.set in Hz.
  destruct_rneq_H.
  inversion Hz; subst.
  eapply regz_exe_delay_stable2; eauto.
  simpl.
  eapply H0 in H11.
  clear - Hexe_delay1 H11 H29.
  sep_star_split_tac.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  rewrite get_R_rn_neq_r0; eauto.
  2 : intro; tryfalse.
  rewrite get_R_rn_neq_r0 in H29; eauto.
  2 : intro; tryfalse.
  lets Hz : H29.
  unfold RegMap.set in Hz.
  unfold merge in Hz.
  destruct_rneq_H.
  inversion Hz; subst.
  eapply regz_exe_delay_stable2; eauto.
  split.
  { 
    intros.
    eapply dly_reduce_asrt_stable in H11; eauto.
    lets Hz : H11.
    eapply H0 in Hz.
    inversion H19; get_ins_diff_false.
    inversion H24; get_ins_diff_false.
    exists fp fq L r.
    lets Hp : H11.
    eapply dly_reduce_asrt_stable in Hp; eauto.
    eapply H1 in Hp; eauto.
    simpljoin1. 
    eapply ins_exec_deterministic in H25; eauto.
    subst.
    assert (bv = v).
    { 
      clear - Hz H30.
      sep_star_split_tac.
      simpls.
      unfolds regSt.
      simpls.
      simpljoin1.
      rewrite get_R_rn_neq_r0 in H30; eauto.
      2 : intro; tryfalse.
      unfold merge in *.
      unfolds RegMap.set.
      destruct_rneq_H.
      inversion H30; subst.
      eauto.
    }
    subst.
    assert (v =ᵢ ($ 0) = false).
    { 
      unfold Int.eq.
      clear - H31.
      destruct (zeq (Int.unsigned v) (Int.unsigned $ 0)) eqn:Heqe; eauto.
      clear Heqe.
      eapply z_eq_to_int_eq in e; eauto.
      do 2 rewrite Int.repr_unsigned in e; eauto.
      subst.
      tryfalse.
    }
    eapply H2 in H14; eauto.
    simpljoin1.
    repeat (split; eauto).
    assert (bv = $ 0).
    {
      clear - Hz H30.
      sep_star_split_tac.
      simpls.
      unfolds regSt.
      simpls.
      simpljoin1.
      rewrite get_R_rn_neq_r0 in H30; eauto.
      2 : intro; tryfalse.
      unfold merge in *.
      unfolds RegMap.set.
      destruct_rneq_H.
      inversion H30; eauto.
    }
    subst.
    tryfalse.
  }
  {
    intros. 
    eapply dly_reduce_asrt_stable in H11; eauto.
    inversion H19; get_ins_diff_false.
    eapply H0 in H11. 
    clear - H11 H30 H31.
    sep_star_split_tac.
    simpls.
    unfolds regSt.
    simpls. 
    simpljoin1. 
    rewrite get_R_rn_neq_r0 in H30; eauto.
    unfold merge in *. 
    unfolds RegMap.set.
    destruct_rneq_H.
    intro; tryfalse.
    inversion H30; subst.
    eapply dly_reduce_asrt_stable in H13; eauto.
    eapply H1 in H13.
    simpljoin1.
    inversion H24; get_ins_diff_false.
    eapply ins_exec_deterministic in H8; eauto.
    subst.  
    clear - H3 H16 H9 H10.
    unfolds insSeq_sound.
    eapply H3; eauto. 
    rewrite Int.add_assoc; eauto.
  }
Qed.

Lemma wf_seq_bne_rule :
  forall p p' q r f1 f2 f i fp fq L I bv Spec,
    Spec (f, f +ᵢ ($ 4)) = Some (fp, fq) -> DlyFrameFree r ->
    (p ↓) ==> z |=> bv ** Atrue ->
    ins_sound ((p ↓) ↓) p' i ->
    (bv =ᵢ ($ 0) = true -> p' ==> fp L ** r /\ fq L ** r ==> q) ->
    (bv =ᵢ ($ 0) = false -> insSeq_sound Spec p' I q) ->
    insSeq_sound Spec p (f1 n> bne f;; f2 n> i;;I) q.
Proof.
  introv H Hr.
  intros.
  unfold insSeq_sound.
  intros.
  inversion H4; subst.
  eapply bne_seq; eauto.
 
  (** progress *)
  destruct_state S.
  assert (exists R' D', exe_delay r0 d = (R', D')).
  {
    eapply exe_delay_no_abort; eauto.
  }
  simpljoin1.
  renames x to R', x0 to D'.
  lets Hp : H6.
  symmetry in Hp.
  eapply dly_reduce_asrt_stable in Hp; eauto.
  assert (exists R'' D'', exe_delay R' D' = (R'', D'')).
  {
    eapply exe_delay_no_abort; eauto.
  }
  simpljoin1.
  renames x to R'', x0 to D''.
  lets Hp' : H7.
  symmetry in Hp'.
  eapply dly_reduce_asrt_stable in Hp'; eauto.
  eapply H1 in Hp'.
  simpljoin1.
  lets Hz : Hp.
  eapply H0 in Hz.
  destruct (Int.eq bv ($ 0)) eqn:Heqe.
  {
    exists (m, (R', f0), D') x f2 f f (f +ᵢ ($ 4)).
    split; eauto. 
    econstructor; eauto.
    eapply Bne_true; eauto.
    clear - Hz Heqe.
    sep_star_split_tac.
    simpls.
    unfolds regSt.
    simpls.
    simpljoin1.
    rewrite get_R_rn_neq_r0; eauto.
    2 : intro; tryfalse.
    unfold merge.
    unfold RegMap.set.
    destruct_rneq.
    eapply int_eq_true_eq in Heqe; eauto.
    subst; eauto.
    destruct_state x.
    econstructor; eauto.
    eapply NTrans; eauto.
  }
  {  
    exists (m, (R', f0), D') x f2 (f2 +ᵢ ($ 4)) (f2 +ᵢ ($ 4)) ((f2 +ᵢ ($ 4)) +ᵢ ($ 4)).
    split; eauto.
    econstructor; eauto. 
    eapply Bne_false with (v := bv) (f := f); eauto.
    clear - Heqe Hz.
    sep_star_split_tac.
    simpls.
    simpljoin1.
    unfolds regSt.
    simpls.
    simpljoin1.
    rewrite get_R_rn_neq_r0; eauto.
    2 : intro; tryfalse.
    unfold merge.
    unfold RegMap.set.
    destruct_rneq.
    clear - Heqe. 
    eapply int_eq_false_neq in Heqe; eauto.
    destruct_state x.
    econstructor; eauto.
    eapply NTrans; eauto.
  }

  (** preservation *)
  intros. 
  inversion H6; subst.
  inversion H7; subst. 
  exists bv.
  split; eauto. 
  lets Hexe_delay1 : H11. 
  eapply dly_reduce_asrt_stable in H11; eauto.
  inversion H19; get_ins_diff_false.
  eapply dly_reduce_asrt_stable in H13; eauto. 
  eapply H0 in H11.   
  clear - Hexe_delay1 H11 H29.
  sep_star_split_tac.
  simpls. 
  unfolds regSt.
  simpls. 
  simpljoin1.
  lets Hz : H29.
  rewrite get_R_rn_neq_r0; eauto.
  2 : intro; tryfalse.
  rewrite get_R_rn_neq_r0 in H29; eauto.
  2 : intro; tryfalse.
  rewrite get_R_rn_neq_r0 in Hz; eauto.
  2 : intro; tryfalse.
  unfold merge in Hz.
  unfold RegMap.set in Hz.
  destruct_rneq_H.
  inversion Hz; subst.
  eapply regz_exe_delay_stable2; eauto.
  simpl.
  rewrite get_R_rn_neq_r0; eauto.
  2 : intro; tryfalse.
  rewrite get_R_rn_neq_r0 in H29; eauto.
  2 : intro; tryfalse.
  eapply H0 in H11. 
  clear - Hexe_delay1 H11 H29.
  sep_star_split_tac.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1. 
  lets Hz : H29.
  unfold RegMap.set in Hz.
  unfold merge in Hz.
  destruct_rneq_H.
  inversion Hz; subst. 
  eapply regz_exe_delay_stable2; eauto.
  split.
  {
    intros.  
    eapply dly_reduce_asrt_stable in H11; eauto.
    lets Hp : H11.
    inversion H19; get_ins_diff_false.
    eapply H0 in H11. 
    exists fp fq L r.
    inversion H24; get_ins_diff_false.
    split; eauto.
    lets Hp' : Hp.
    eapply dly_reduce_asrt_stable in Hp'; eauto.
    eapply H1 in Hp'; eauto.
    simpljoin1.
    eapply ins_exec_deterministic in H23; eauto.
    subst.
    assert (($ 0) =ᵢ ($ 0) = true).
    eauto.
    eapply H2 in H10.
    simpljoin1.
    repeat (split; eauto).
    eapply H0 in Hp.
    clear - Hp H30 H31.
    sep_star_split_tac.
    simpls.
    unfolds regSt.
    simpls.
    simpljoin1.
    rewrite get_R_rn_neq_r0 in H30; eauto.
    2 : intro; tryfalse.
    unfold merge in *.
    unfolds RegMap.set.
    destruct_rneq_H.
  }
  {
    intros.
    lets Hz : H11. 
    eapply dly_reduce_asrt_stable in Hz; eauto.
    lets Hp : Hz.
    inversion H19; get_ins_diff_false.  
    eapply H0 in Hz.
    clear - Hz H8 H30.
    sep_star_split_tac.
    simpls.
    unfolds regSt.
    simpls.
    simpljoin1.
    rewrite get_R_rn_neq_r0 in H30; eauto.
    2 : intro; tryfalse.
    unfold merge in *.
    unfolds RegMap.set.
    destruct_rneq_H.
    eapply H0 in Hz.
    assert (bv = v).
    { 
      clear - Hz H30.
      sep_star_split_tac.
      simpls. 
      unfolds regSt.
      simpls.
      simpljoin1.
      rewrite get_R_rn_neq_r0 in H30; eauto.
      2 : intro; tryfalse.
      unfold merge in *.
      unfolds RegMap.set.
      destruct_rneq_H.
      inversion H30; subst.
      eauto.
    }
    subst.
    inversion H24; get_ins_diff_false.
    eapply dly_reduce_asrt_stable in H13; eauto.
    eapply H1 in H13; eauto.
    simpljoin1.
    eapply ins_exec_deterministic in H25; eauto.
    subst. 
    unfold insSeq_sound in H3.
    eapply H3; eauto.
    clear - H10 Hz H30 H31.
    unfold Int.eq.
    destruct (zeq (Int.unsigned v) (Int.unsigned $ 0)); eauto.
    eapply z_eq_to_int_eq in e; eauto. 
    do 2 rewrite Int.repr_unsigned in e; tryfalse.
    clear - H16.
    rewrite Int.add_assoc; eauto.
  }
Qed.
  
Theorem wf_seq_frame_rule :
  forall p q r I Spec,
    insSeq_sound Spec p I q -> DlyFrameFree r ->
    insSeq_sound Spec (p ** r) I (q ** r).
Proof.
  intros.
  unfolds insSeq_sound.
  intros.
  lets HI : H1.
  sep_star_split_tac.
  simpl in H6.
  simpljoin1.
  eapply H in H2; eauto.
  eapply safety_ins_seq_frame_property; eauto.
Qed.

Theorem wf_seq_conseq_rule :
  forall I p p1 q1 q Spec,
    p ==> p1 -> q1 ==> q -> insSeq_sound Spec p1 I q1 ->
    insSeq_sound Spec p I q.
Proof.
  intros.
  unfolds insSeq_sound.
  intros.
  lets HI : H2.
  eapply H1 in HI; eauto.
  eapply safety_ins_seq_post_weak; eauto.
Qed.

Theorem wf_seq_ex_intro_rule :
  forall tp (p : tp -> asrt) I q Spec,
    (forall x' : tp, insSeq_sound Spec (p x') I q) ->
    insSeq_sound Spec (EX x : tp, p x) I q.
Proof.
  intros.
  unfold insSeq_sound.
  intros.
  simpls.
  simpljoin1.
  specialize (H x).
  unfolds insSeq_sound.
  eauto.
Qed.

Theorem wf_seq_disj_rule :
  forall p1 p2 q1 q2 I Spec,
    insSeq_sound Spec p1 I q1 -> insSeq_sound Spec p2 I q2 ->
    insSeq_sound Spec (p1 \\// p2) I (q1 \\// q2).
Proof.
  intros.
  unfolds insSeq_sound.
  intros.
  simpl in H2.
  simpljoin1. 
  destruct H2; eauto.
  eapply safety_ins_seq_post_disj1; eauto.
  eapply safety_ins_seq_post_disj2; eauto.
Qed.

Lemma wf_seq_pure_intro_rule :
  forall p q (pu : Prop) I Spec,
    (pu -> insSeq_sound Spec p I q) ->
    insSeq_sound Spec ([| pu |] ** p) I q.
Proof.
  intros.
  unfolds insSeq_sound.
  intros.
  sep_star_split_tac.
  simpl in H5.
  simpljoin1.
  simpl in H1.
  simpljoin1.
  rewrite empM_merge_still_l; eauto.
Qed.
  
Theorem wf_seq_sound :
  forall Spec p q I,
    wf_seq Spec p I q ->
    insSeq_sound Spec p I q.
Proof.
  intros.
  induction H; intros.

  -
    eapply ins_rule_sound in H.
    eapply wf_seq_seq_rule; eauto.

  -
    eapply ins_rule_sound in H1.
    eapply wf_seq_call_rule; eauto.

  -
    eapply ins_rule_sound in H.
    eapply wf_seq_ret_rule; eauto.

  -
    eapply ins_rule_sound in H2.
    eapply wf_seq_j1_rule; eauto.

  -
    eapply wf_seq_J2_rule; eauto.

  -   
    eapply ins_rule_sound in H0.
    eapply wf_seq_be_rule; eauto.

  -
    eapply ins_rule_sound in H0.
    eapply wf_seq_bne_rule; eauto.

  -
    unfold insSeq_sound.
    intros.
    simpl in H0.
    tryfalse.

  -
    eapply wf_seq_frame_rule; eauto.

  -
    eapply wf_seq_ex_intro_rule; eauto.

  -
    eapply wf_seq_conseq_rule; eauto.

  -
    eapply wf_seq_disj_rule; eauto.

  -
    eapply wf_seq_pure_intro_rule; eauto.
Qed.