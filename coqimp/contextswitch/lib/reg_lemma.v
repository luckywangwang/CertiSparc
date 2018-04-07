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
  
Open Scope nat.
Open Scope code_scope.
Open Scope mem_scope.

(*+ Auxiliary Definition +*)
Definition update_frame (fm : Frame) (n : nat) (v : Word) :=
  match fm with
  | consfm w0 w1 w2 w3 w4 w5 w6 w7 =>
    match n with
    | 0 => consfm v w1 w2 w3 w4 w5 w6 w7
    | 1 => consfm w0 v w2 w3 w4 w5 w6 w7
    | 2 => consfm w0 w1 v w3 w4 w5 w6 w7
    | 3 => consfm w0 w1 w2 v w4 w5 w6 w7
    | 4 => consfm w0 w1 w2 w3 v w5 w6 w7
    | 5 => consfm w0 w1 w2 w3 w4 v w6 w7
    | 6 => consfm w0 w1 w2 w3 w4 w5 v w7
    | 7 => consfm v w1 w2 w3 w4 w5 w6 v
    | _ => consfm w0 w1 w2 w3 w4 w5 w6 w7
    end
  end.

Definition get_frame_nth (fm : Frame) (n : nat) :=
  match fm with
  | consfm w0 w1 w2 w3 w4 w5 w6 w7 =>
    match n with
    | 0 => Some w0
    | 1 => Some w1
    | 2 => Some w2
    | 3 => Some w3
    | 4 => Some w4
    | 5 => Some w5
    | 6 => Some w6
    | 7 => Some w7
    | _ => None
    end
  end.

Definition get_frame_nth' (fm : Frame) (n : nat) :=
  match fm with
  | consfm w0 w1 w2 w3 w4 w5 w6 w7 =>
    match n with
    | 0 => w0
    | 1 => w1
    | 2 => w2
    | 3 => w3
    | 4 => w4
    | 5 => w5
    | 6 => w6
    | 7 => w7
    | _ => ($ 0)
    end
  end.

Definition GenRegState : Type := Frame * Frame * Frame * Frame.

Fixpoint upd_genreg (greg_st : GenRegState) (rr : GenReg) (w : Word) : GenRegState :=
  match greg_st with
  | (fmg, fmo, fml, fmi) =>
    match rr with
    | r0 => (update_frame fmg 0 w, fmo, fml, fmi)
    | r1 => (update_frame fmg 1 w, fmo, fml, fmi)
    | r2 => (update_frame fmg 2 w, fmo, fml, fmi)
    | r3 => (update_frame fmg 3 w, fmo, fml, fmi)
    | r4 => (update_frame fmg 4 w, fmo, fml, fmi)
    | r5 => (update_frame fmg 5 w, fmo, fml, fmi)
    | r6 => (update_frame fmg 6 w, fmo, fml, fmi)
    | r7 => (update_frame fmg 7 w, fmo, fml, fmi)
    | r8 => (fmg, update_frame fmo 0 w, fml, fmi)
    | r9 => (fmg, update_frame fmo 1 w, fml, fmi)
    | r10 => (fmg, update_frame fmo 2 w, fml, fmi)
    | r11 => (fmg, update_frame fmo 3 w, fml, fmi)
    | r12 => (fmg, update_frame fmo 4 w, fml, fmi)
    | r13 => (fmg, update_frame fmo 5 w, fml, fmi)
    | r14 => (fmg, update_frame fmo 6 w, fml, fmi)
    | r15 => (fmg, update_frame fmo 7 w, fml, fmi)
    | r16 => (fmg, fmo, update_frame fml 0 w, fmi)
    | r17 => (fmg, fmo, update_frame fml 1 w, fmi)
    | r18 => (fmg, fmo, update_frame fml 2 w, fmi)
    | r19 => (fmg, fmo, update_frame fml 3 w, fmi)
    | r20 => (fmg, fmo, update_frame fml 4 w, fmi)
    | r21 => (fmg, fmo, update_frame fml 5 w, fmi)
    | r22 => (fmg, fmo, update_frame fml 6 w, fmi)
    | r23 => (fmg, fmo, update_frame fml 7 w, fmi)
    | r24 => (fmg, fmo, fml, update_frame fmi 0 w)
    | r25 => (fmg, fmo, fml, update_frame fmi 1 w)
    | r26 => (fmg, fmo, fml, update_frame fmi 2 w)
    | r27 => (fmg, fmo, fml, update_frame fmi 3 w)
    | r28 => (fmg, fmo, fml, update_frame fmi 4 w)
    | r29 => (fmg, fmo, fml, update_frame fmi 5 w)
    | r30 => (fmg, fmo, fml, update_frame fmi 6 w)
    | r31 => (fmg, fmo, fml, update_frame fmi 7 w)
    end
  end.

Definition get_global_frame (fm : Frame) (rr : GenReg) :=
  match rr with
  | r0 => Some ($ 0)
  | r1 => get_frame_nth fm 1
  | r2 => get_frame_nth fm 2
  | r3 => get_frame_nth fm 3
  | r4 => get_frame_nth fm 4
  | r5 => get_frame_nth fm 5
  | r6 => get_frame_nth fm 6
  | r7 => get_frame_nth fm 7
  | _ => None
  end.

Definition get_out_frame (fm : Frame) (rr : GenReg) :=
  match rr with
  | r8 => get_frame_nth fm 0
  | r9 => get_frame_nth fm 1
  | r10 => get_frame_nth fm 2
  | r11 => get_frame_nth fm 3
  | r12 => get_frame_nth fm 4
  | r13 => get_frame_nth fm 5
  | r14 => get_frame_nth fm 6
  | r15 => get_frame_nth fm 7
  | _ => None
  end.

Definition get_local_frame (fm : Frame) (rr : GenReg) :=
  match rr with
  | r16 => get_frame_nth fm 0
  | r17 => get_frame_nth fm 1
  | r18 => get_frame_nth fm 2
  | r19 => get_frame_nth fm 3
  | r20 => get_frame_nth fm 4
  | r21 => get_frame_nth fm 5
  | r22 => get_frame_nth fm 6
  | r23 => get_frame_nth fm 7
  | _ => None
  end.

Definition get_in_frame (fm : Frame) (rr : GenReg) :=
  match rr with
  | r24 => get_frame_nth fm 0
  | r25 => get_frame_nth fm 1
  | r26 => get_frame_nth fm 2
  | r27 => get_frame_nth fm 3
  | r28 => get_frame_nth fm 4
  | r29 => get_frame_nth fm 5
  | r30 => get_frame_nth fm 6
  | r31 => get_frame_nth fm 7
  | _ => None
  end.
    
Fixpoint get_genreg_val (greg_st : GenRegState) (rr : GenReg) : Word :=
  match greg_st with
  | (fmg, fmo, fml, fmi) =>
    match rr with
    | r0 => ($ 0)
    | r1 => get_frame_nth' fmg 1
    | r2 => get_frame_nth' fmg 2
    | r3 => get_frame_nth' fmg 3
    | r4 => get_frame_nth' fmg 4
    | r5 => get_frame_nth' fmg 5
    | r6 => get_frame_nth' fmg 6
    | r7 => get_frame_nth' fmg 7
    | r8 => get_frame_nth' fmo 0
    | r9 => get_frame_nth' fmo 1
    | r10 => get_frame_nth' fmo 2
    | r11 => get_frame_nth' fmo 3
    | r12 => get_frame_nth' fmo 4
    | r13 => get_frame_nth' fmo 5
    | r14 => get_frame_nth' fmo 6
    | r15 => get_frame_nth' fmo 7
    | r16 => get_frame_nth' fml 0
    | r17 => get_frame_nth' fml 1
    | r18 => get_frame_nth' fml 2
    | r19 => get_frame_nth' fml 3
    | r20 => get_frame_nth' fml 4
    | r21 => get_frame_nth' fml 5
    | r22 => get_frame_nth' fml 6
    | r23 => get_frame_nth' fml 7
    | r24 => get_frame_nth' fmi 0
    | r25 => get_frame_nth' fmi 1
    | r26 => get_frame_nth' fmi 2
    | r27 => get_frame_nth' fmi 3
    | r28 => get_frame_nth' fmi 4
    | r29 => get_frame_nth' fmi 5
    | r30 => get_frame_nth' fmi 6
    | r31 => get_frame_nth' fmi 7
    end
  end.

Definition GlobalRegs (fm : Frame) :=
  match fm with
  | consfm w0 w1 w2 w3 w4 w5 w6 w7 =>
    r0 |=> w0 ** r1 |=> w1 ** r2 |=> w2 ** r3 |=> w3 ** r4 |=> w4 **
       r5 |=> w5 ** r6 |=> w6 ** r7 |=> w7
  end.

Definition GenRegs (grst : GenRegState) : asrt :=
  match grst with
  | (fmg, fmo, fml, fmi) =>
    GlobalRegs fmg ** OutRegs fmo ** LocalRegs fml ** InRegs fmi
  end.

Definition eval_opexp_reg (grst : GenRegState) (a : OpExp) :=
  match a with
  | Or r => Some (get_genreg_val grst r)
  | Ow w => if ($ (-4096)) <=ᵢ w && w <=ᵢ ($ 4095) then Some w else None
  end.

Lemma get_global_frame_get_R :
  forall fm p M R F D v (rr : GenReg),
    (M, (R, F), D) |= GlobalRegs fm ** p ->
    get_global_frame fm rr = Some v ->
    get_R R rr = Some v.
Proof.
  intros.
  sep_star_split_tac.
  simpl in H4.
  simpljoin1.
  unfolds GlobalRegs.
  destruct fm.
  destruct rr; simpl in H0; tryfalse;
    try inversion H0; subst; try eapply get_R_merge_still; unfold get_R.

  eapply rn_st_v_eval_reg_v in H.
  rewrite H; eauto.

  simpl_sep_liftn_in H 2.
  eapply rn_st_v_eval_reg_v in H.
  rewrite H; eauto.

  simpl_sep_liftn_in H 3.
  eapply rn_st_v_eval_reg_v in H.
  rewrite H; eauto.

  simpl_sep_liftn_in H 4.
  eapply rn_st_v_eval_reg_v in H.
  rewrite H; eauto.

  simpl_sep_liftn_in H 5.
  eapply rn_st_v_eval_reg_v in H.
  rewrite H; eauto.

  simpl_sep_liftn_in H 6.
  eapply rn_st_v_eval_reg_v in H.
  rewrite H; eauto.

  simpl_sep_liftn_in H 7.
  eapply rn_st_v_eval_reg_v in H.
  rewrite H; eauto.

  simpl_sep_liftn_in H 8.
  eapply rn_st_v_eval_reg_v in H.
  rewrite H; eauto.
Qed.

Lemma get_out_frame_get_R :
  forall fm p M R F D v (rr : GenReg),
    (M, (R, F), D) |= OutRegs fm ** p ->
    get_out_frame fm rr = Some v ->
    get_R R rr = Some v.
Proof.
  intros.
  sep_star_split_tac.
  simpl in H4.
  simpljoin1.
  unfolds OutRegs.
  destruct fm.
  destruct rr; simpl in H0; tryfalse;
    try inversion H0; subst; try eapply get_R_merge_still; unfold get_R.
 
  eapply rn_st_v_eval_reg_v in H.
  rewrite H; eauto.

  simpl_sep_liftn_in H 2.
  eapply rn_st_v_eval_reg_v in H.
  rewrite H; eauto.

  simpl_sep_liftn_in H 3.
  eapply rn_st_v_eval_reg_v in H.
  rewrite H; eauto.

  simpl_sep_liftn_in H 4.
  eapply rn_st_v_eval_reg_v in H.
  rewrite H; eauto.

  simpl_sep_liftn_in H 5.
  eapply rn_st_v_eval_reg_v in H.
  rewrite H; eauto.

  simpl_sep_liftn_in H 6.
  eapply rn_st_v_eval_reg_v in H.
  rewrite H; eauto.

  simpl_sep_liftn_in H 7.
  eapply rn_st_v_eval_reg_v in H.
  rewrite H; eauto.

  simpl_sep_liftn_in H 8.
  eapply rn_st_v_eval_reg_v in H.
  rewrite H; eauto.
Qed.

Lemma get_local_frame_get_R :
  forall fm p M R F D v (rr : GenReg),
    (M, (R, F), D) |= LocalRegs fm ** p ->
    get_local_frame fm rr = Some v ->
    get_R R rr = Some v.
Proof.
  intros.
  sep_star_split_tac.
  simpl in H4.
  simpljoin1.
  unfolds LocalRegs.
  destruct fm.
  destruct rr; simpl in H0; tryfalse;
    try inversion H0; subst; try eapply get_R_merge_still; unfold get_R.
 
  eapply rn_st_v_eval_reg_v in H.
  rewrite H; eauto.

  simpl_sep_liftn_in H 2.
  eapply rn_st_v_eval_reg_v in H.
  rewrite H; eauto.

  simpl_sep_liftn_in H 3.
  eapply rn_st_v_eval_reg_v in H.
  rewrite H; eauto.

  simpl_sep_liftn_in H 4.
  eapply rn_st_v_eval_reg_v in H.
  rewrite H; eauto.

  simpl_sep_liftn_in H 5.
  eapply rn_st_v_eval_reg_v in H.
  rewrite H; eauto.

  simpl_sep_liftn_in H 6.
  eapply rn_st_v_eval_reg_v in H.
  rewrite H; eauto.

  simpl_sep_liftn_in H 7.
  eapply rn_st_v_eval_reg_v in H.
  rewrite H; eauto.

  simpl_sep_liftn_in H 8.
  eapply rn_st_v_eval_reg_v in H.
  rewrite H; eauto.
Qed.

Lemma get_in_frame_get_R :
  forall fm p M R F D v (rr : GenReg),
    (M, (R, F), D) |= InRegs fm ** p ->
    get_in_frame fm rr = Some v ->
    get_R R rr = Some v.
Proof.
  intros.
  sep_star_split_tac.
  simpl in H4.
  simpljoin1.
  unfolds OutRegs.
  destruct fm.
  destruct rr; simpl in H0; tryfalse;
    try inversion H0; subst; try eapply get_R_merge_still; unfold get_R.
 
  eapply rn_st_v_eval_reg_v in H.
  rewrite H; eauto.

  simpl_sep_liftn_in H 2.
  eapply rn_st_v_eval_reg_v in H.
  rewrite H; eauto.

  simpl_sep_liftn_in H 3.
  eapply rn_st_v_eval_reg_v in H.
  rewrite H; eauto.

  simpl_sep_liftn_in H 4.
  eapply rn_st_v_eval_reg_v in H.
  rewrite H; eauto.

  simpl_sep_liftn_in H 5.
  eapply rn_st_v_eval_reg_v in H.
  rewrite H; eauto.

  simpl_sep_liftn_in H 6.
  eapply rn_st_v_eval_reg_v in H.
  rewrite H; eauto.

  simpl_sep_liftn_in H 7.
  eapply rn_st_v_eval_reg_v in H.
  rewrite H; eauto.

  simpl_sep_liftn_in H 8.
  eapply rn_st_v_eval_reg_v in H.
  rewrite H; eauto.
Qed.
  
Lemma getR_eq_get_genreg_val :
  forall M R F D grst (rr : GenReg),
    (M, (R, F), D) |= GenRegs grst ->
    get_R R rr = Some (get_genreg_val grst rr).
Proof.
  intros.
  unfolds GenRegs.
  destruct grst.
  destruct p.
  destruct p.
  destruct f1, f2, f0, f.
  destruct rr; simpl;
    try solve [eapply get_global_frame_get_R; [eauto | simpl; eauto] ];
    try solve [simpl_sep_liftn_in H 2;
               eapply get_out_frame_get_R; [eauto | simpl; eauto] ];
    try solve [simpl_sep_liftn_in H 3;
               eapply get_local_frame_get_R; [eauto | simpl; eauto] ];
    try solve [sliftn_in H 4;
               eapply get_in_frame_get_R; [eauto | simpl; eauto] ].
Qed.

Lemma eval_opexp_reg_eq_eval_opexp :
  forall M R F D grst oexp v,
    (M, (R, F), D) |= GenRegs grst ->
    eval_opexp_reg grst oexp = Some v ->
    eval_opexp R oexp = Some v.
Proof.
  intros.
  unfolds GenRegs.
  destruct grst.
  destruct p.
  destruct p.
  destruct f1, f2, f0, f.
  destruct oexp; simpl in H0.
  destruct g; inversion H0; subst; simpl;
    try solve [eapply get_global_frame_get_R; [eauto | simpl; eauto] ];
    try solve [simpl_sep_liftn_in H 2;
               eapply get_out_frame_get_R; [eauto | simpl; eauto] ];
    try solve [simpl_sep_liftn_in H 3;
               eapply get_local_frame_get_R; [eauto | simpl; eauto] ];
    try solve [sliftn_in H 4;
               eapply get_in_frame_get_R; [eauto | simpl; eauto] ].
  destruct (($ (-4096)) <=ᵢ w31 && w31 <=ᵢ ($ 4095)) eqn:Heqe; eauto;
    inversion H0; subst; eauto.
  simpl; eauto.
  rewrite Heqe; eauto.
Qed.

Ltac asrt_to_line_in H t :=
  match type of H with
  | _ |= ?p1 ** ?p2 =>
    eapply asrt_combine_to_line_stable with (n := t) in H;
    unfold asrt_combine_to_line in H; fold asrt_combine_to_line in H
  | _ => idtac
  end.

Definition globalRegs_rm_one (fm : Frame) (rr : GenReg) :=
  match fm with
  | consfm w0 w1 w2 w3 w4 w5 w6 w7 =>
    match rr with
    | r0 =>
      r1 |=> w1 ** r2 |=> w2 ** r3 |=> w3 **
         r4 |=> w4 ** r5 |=> w5 ** r6 |=> w6 ** r7 |=> w7
    | r1 =>
      r0 |=> w0 ** r2 |=> w2 ** r3 |=> w3 **
         r4 |=> w4 ** r5 |=> w5 ** r6 |=> w6 ** r7 |=> w7
    | r2 =>
      r0 |=> w0 ** r1 |=> w1 ** r3 |=> w3 **
         r4 |=> w4 ** r5 |=> w5 ** r6 |=> w6 ** r7 |=> w7
    | r3 =>
      r0 |=> w0 ** r1 |=> w1 ** r2 |=> w2 **
         r4 |=> w4 ** r5 |=> w5 ** r6 |=> w6 ** r7 |=> w7
    | r4 =>
      r0 |=> w0 ** r1 |=> w1 ** r2 |=> w2 **
         r3 |=> w3 ** r5 |=> w5 ** r6 |=> w6 ** r7 |=> w7
    | r5 =>
      r0 |=> w0 ** r1 |=> w1 ** r2 |=> w2 **
         r3 |=> w3 ** r4 |=> w4 ** r6 |=> w6 ** r7 |=> w7
    | r6 =>
      r0 |=> w0 ** r1 |=> w1 ** r2 |=> w2 **
         r3 |=> w3 ** r4 |=> w4 ** r5 |=> w5 ** r7 |=> w7
    | r7 =>
      r0 |=> w0 ** r1 |=> w1 ** r2 |=> w2 **
         r3 |=> w3 ** r4 |=> w4 ** r5 |=> w5 ** r6 |=> w6
    | _ =>
      r0 |=> w0 ** r1 |=> w1 ** r2 |=> w2 **
         r3 |=> w3 ** r4 |=> w4 ** r5 |=> w5 ** r6 |=> w6 ** r7 |=> w7
    end
  end.

Definition outRegs_rm_one (fm : Frame) (rr : GenReg) :=
  match fm with
  | consfm w0 w1 w2 w3 w4 w5 w6 w7 =>
    match rr with
    | r8 =>
      r9 |=> w1 ** r10 |=> w2 ** r11 |=> w3 **
         r12 |=> w4 ** r13 |=> w5 ** r14 |=> w6 ** r15 |=> w7
    | r9 =>
      r8 |=> w0 ** r10 |=> w2 ** r11 |=> w3 **
         r12 |=> w4 ** r13 |=> w5 ** r14 |=> w6 ** r15 |=> w7
    | r10 =>
      r8 |=> w0 ** r9 |=> w1 ** r11 |=> w3 **
         r12 |=> w4 ** r13 |=> w5 ** r14 |=> w6 ** r15 |=> w7
    | r11 =>
      r8 |=> w0 ** r9 |=> w1 ** r10 |=> w2 **
         r12 |=> w4 ** r13 |=> w5 ** r14 |=> w6 ** r15 |=> w7
    | r12 =>
      r8 |=> w0 ** r9 |=> w1 ** r10 |=> w2 **
         r11 |=> w3 ** r13 |=> w5 ** r14 |=> w6 ** r15 |=> w7
    | r13 =>
      r8 |=> w0 ** r9 |=> w1 ** r10 |=> w2 **
         r11 |=> w3 ** r12 |=> w4 ** r14 |=> w6 ** r15 |=> w7
    | r14 =>
      r8 |=> w0 ** r9 |=> w1 ** r10 |=> w2 **
         r11 |=> w3 ** r12 |=> w4 ** r13 |=> w5 ** r15 |=> w7
    | r15 =>
      r8 |=> w0 ** r9 |=> w1 ** r10 |=> w2 **
         r11 |=> w3 ** r12 |=> w4 ** r13 |=> w5 ** r14 |=> w6
    | _ =>
      r8 |=> w0 ** r9 |=> w1 ** r10 |=> w2 **
         r11 |=> w3 ** r12 |=> w4 ** r13 |=> w5 ** r14 |=> w6 ** r15 |=> w7
    end
  end.

Definition localRegs_rm_one (fm : Frame) (rr : GenReg) :=
  match fm with
  | consfm w0 w1 w2 w3 w4 w5 w6 w7 =>
    match rr with
    | r16 =>
      r17 |=> w1 ** r18 |=> w2 ** r19 |=> w3 **
         r20 |=> w4 ** r21 |=> w5 ** r22 |=> w6 ** r23 |=> w7
    | r17 =>
      r16 |=> w0 ** r18 |=> w2 ** r19 |=> w3 **
         r20 |=> w4 ** r21 |=> w5 ** r22 |=> w6 ** r23 |=> w7
    | r18 =>
      r16 |=> w0 ** r17 |=> w1 ** r19 |=> w3 **
         r20 |=> w4 ** r21 |=> w5 ** r22 |=> w6 ** r23 |=> w7
    | r19 =>
      r16 |=> w0 ** r17 |=> w1 ** r18 |=> w2 **
         r20 |=> w4 ** r21 |=> w5 ** r22 |=> w6 ** r23 |=> w7
    | r20 =>
      r16 |=> w0 ** r17 |=> w1 ** r18 |=> w2 **
         r19 |=> w3 ** r21 |=> w5 ** r22 |=> w6 ** r23 |=> w7
    | r21 =>
      r16 |=> w0 ** r17 |=> w1 ** r18 |=> w2 **
         r19 |=> w3 ** r20 |=> w4 ** r22 |=> w6 ** r23 |=> w7
    | r22 =>
      r16 |=> w0 ** r17 |=> w1 ** r18 |=> w2 **
          r19 |=> w3 ** r20 |=> w4 ** r21 |=> w5 ** r23 |=> w7
    | r23 =>
      r16 |=> w0 ** r17 |=> w1 ** r18 |=> w2 **
          r19 |=> w3 ** r20 |=> w4 ** r21 |=> w5 ** r22 |=> w6
    | _ =>
      r16 |=> w0 ** r17 |=> w1 ** r18 |=> w2 ** r19 |=> w3 **
         r20 |=> w4 ** r21 |=> w5 ** r22 |=> w6 ** r23 |=> w7
    end
  end.

Definition inRegs_rm_one (fm : Frame) (rr : GenReg) :=
  match fm with
  | consfm w0 w1 w2 w3 w4 w5 w6 w7 =>
    match rr with
    | r24 =>
      r25 |=> w1 ** r26 |=> w2 ** r27 |=> w3 **
         r28 |=> w4 ** r29 |=> w5 ** r30 |=> w6 ** r31 |=> w7
    | r25 =>
      r24 |=> w0 ** r26 |=> w2 ** r27 |=> w3 **
         r28 |=> w4 ** r29 |=> w5 ** r30 |=> w6 ** r31 |=> w7
    | r26 =>
      r24 |=> w0 ** r25 |=> w1 ** r26 |=> w2 **
         r28 |=> w4 ** r29 |=> w5 ** r30 |=> w6 ** r31 |=> w7
    | r27 =>
      r24 |=> w0 ** r25 |=> w1 ** r26 |=> w2 **
         r28 |=> w4 ** r29 |=> w5 ** r30 |=> w6 ** r31 |=> w7
    | r28 =>
      r24 |=> w0 ** r25 |=> w1 ** r26 |=> w2 **
          r27 |=> w3 ** r29 |=> w5 ** r30 |=> w6 ** r31 |=> w7
    | r29 =>
      r24 |=> w0 ** r25 |=> w1 ** r26 |=> w2 **
          r27 |=> w3 ** r28 |=> w4 ** r30 |=> w6 ** r31 |=> w7
    | r30 =>
      r24 |=> w0 ** r25 |=> w1 ** r26 |=> w2 **
          r27 |=> w3 ** r28 |=> w4 ** r29 |=> w5 ** r31 |=> w7
    | r31 =>
      r24 |=> w0 ** r25 |=> w1 ** r26 |=> w2 **
          r27 |=> w3 ** r28 |=> w4 ** r29 |=> w5 ** r30 |=> w6
    | _ =>
      r24 |=> w0 ** r25 |=> w1 ** r26 |=> w2 ** r27 |=> w3 **
         r28 |=> w4 ** r29 |=> w5 ** r30 |=> w6 ** r31 |=> w7
    end
  end.

Definition GenRegs_rm_one (greg_st : GenRegState) (rr : GenReg) :=
  match greg_st with
  | (fmg, fmo, fml, fmi) =>
    globalRegs_rm_one fmg rr ** outRegs_rm_one fmo rr **
                      localRegs_rm_one fml rr ** inRegs_rm_one fmi rr
  end.

Lemma GenRegs_split_one :
  forall s grst p (rr : GenReg),
    s |= GenRegs grst ** p ->
    s |= rr |=> get_genreg_val grst rr ** GenRegs_rm_one grst rr ** p.
Proof.
  intros.
  unfolds GenRegs.
  destruct grst.
  destruct p0.
  destruct p0.
  destruct f1, f2, f0, f.
  destruct rr.
  {
    simpl get_genreg_val.
    simpl GenRegs_rm_one.
    unfold GlobalRegs, OutRegs, LocalRegs, InRegs in H.
    >>>>>>>>>>>>>>>>>>>>
  }
  
Theorem add_rule_reg :
  forall grst rs rd p oexp v1 v2,
    get_genreg_val grst rs = v1 -> eval_opexp_reg grst oexp = Some v2 ->
    |- {{ GenRegs grst ** p }} add rs oexp rd
                              {{ GenRegs (upd_genreg grst rd (v1 +ᵢ v2)) ** p }}.
Proof.
  intros.
  eapply ins_conseq_rule.
  eauto.
  eapply add_rule; eauto.
  {
    intros.
    simpl.
    split.
    {
      instantiate (1 := v1).
      sep_star_split_tac.
      simpl in H5.
      simpljoin1.
      simpl.
      eapply getR_eq_get_genreg_val in H1; eauto.
      eapply get_R_merge_still; eauto.
    }
    {
      instantiate (1 := v2).
      sep_star_split_tac.
      simpl in H5.
      simpljoin1.
      simpl.
      eapply eval_opexp_merge_still; eauto.
      eapply eval_opexp_reg_eq_eval_opexp; eauto.
    }
  }
  {  
    intros.
    instantiate (2 := (get_genreg_val grst rd)).
    instantiate (1 := (GenRegs_rm_one grst rd ** p)).
  }
  
                         