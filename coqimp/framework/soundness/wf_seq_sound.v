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
    eapply regz_exe_delay_stable in H3; eauto.
    rewrite H27 in H3.
    inversion H3; subst.
    tryfalse.
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
    eapply regz_exe_delay_stable in H3; eauto.
    rewrite H28 in H3.
    inversion H3; subst.
    tryfalse.
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
      
    }
    

(*+ Instruction Sequence Rule Sound +*) 
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

Theorem wf_seq_sound :
  forall Spec p q I,
    wf_seq Spec p I q ->
    insSeq_sound Spec p I q.
Proof.
  intros.
  induction H; intros.
  Focus 10.
Admitted.
