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

Require Import sep_lemma.
Require Import reg_lemma.

Require Import code.

Require Import Coq.Logic.FunctionalExtensionality.
  
Open Scope nat.
Open Scope code_scope.
Open Scope mem_scope.

(*+ Stack +*)
Definition stack_seg (l : Address) (fm : Frame) :=
  match fm with
  | consfm w0 w1 w2 w3 w4 w5 w6 w7 =>
    l |-> w0 ** (l +ᵢ ($ 4)) |-> w1 ** (l +ᵢ ($ 8)) |-> w2 ** (l +ᵢ ($ 12)) |-> w3 **
      (l +ᵢ ($ 16)) |-> w4 ** (l +ᵢ ($ 20)) |-> w5 ** (l +ᵢ ($ 24)) |-> w6 ** (l +ᵢ ($ 28)) |-> w7
  end.
      
(** a stack frame saves local and in registers *)
Definition stack_frame (l : Address) (fml fmi : Frame) :=
  stack_seg l fml ** stack_seg (l +ᵢ ($ 32)) fmi.

(** a stack is composed by stack frames *)
Fixpoint stack' (l : Address) (lfp : list (Frame * Frame)) :=
  match lfp with
  | (fml, fmi) :: lfp' =>
    stack_frame l fml fmi ** stack' (l -ᵢ ($ 64)) lfp'
  | nil => Aemp
  end.

Definition stack (st : stack_val) :=
  match st with
  | (l, lfp) => stack' l lfp
  end.

(*+ Context +*)
Fixpoint save_reg (l : Address) (n : nat) (vl : list Word) :=
  match n with
  | 0 => match vl with
        | nil => Aemp
        | _ => Afalse
        end
  | S n' =>
    match vl with
    | nil => Afalse
    | v :: vl' => l |-> v ** save_reg (l +ᵢ ($ 4)) n' vl'
    end
  end.

(** context is a segment in TCB, saves %l0 ~ %l3, %i0 ~ %i7, %g0 ~ %g7, Y 
when occurring ctxswitch *)

Definition context' (l : Address) (rl ri rg: list Word) (ry : Word) :=
  save_reg l 4 rl ** save_reg (l +ᵢ ($ 16)) 8 ri ** save_reg (l +ᵢ ($ 48)) 8 rg **
  (l +ᵢ ($ 80)) |-> ry.

Definition context (ctx : ctx_val) :=
  match ctx with
  | (l, (rl, ri, rg, ry)) =>
    context' l rl ri rg ry
  end.

Fixpoint nth_val (n : nat) (vl : list Word) {struct vl}:=
  match vl with
    | nil => None
    | v::vl' => match n with
                  | 0 => Some v
                  | S n' => nth_val n' vl'
                end
  end.

(*+ Auxiliary Operation +*)
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

Definition frame_to_list (fm : Frame) :=
  match fm with
  | consfm w0 w1 w2 w3 w4 w5 w6 w7 =>
    w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: nil
  end.

Definition list_to_frame (ls : list Word) :=
  match ls with
  | w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: nil =>
    Some (consfm w0 w1 w2 w3 w4 w5 w6 w7)
  | _ => None
  end.

Definition get_global_valid (fm : Frame) :=
  match fm with
  | consfm w0 w1 w2 w3 w4 w5 w6 w7 =>
    w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: nil
  end.

Definition get_local_valid (fm : Frame) :=
  match fm with
  | consfm w0 w1 w2 w3 w4 w5 w6 w7 =>
    w0 :: w1 :: w2 :: w3 :: nil
  end.

Fixpoint get_list_pre {A : Type} (ls : list A) (n : nat) :=
  match n with
  | 0 => nil
  | S n' => match ls with
           | v :: ls' => v :: get_list_pre ls' n'
           | nil => nil
           end
  end.

Definition get_ctx_addr (ctx : ctx_val) :=
  match ctx with
  | (addr, _) => addr
  end.

Definition get_ctx_l (ctx : ctx_val) :=
  match ctx with
  | (addr, (cl, ci, cg)) => cl
  end.

Definition get_ctx_i (ctx : ctx_val) :=
  match ctx with
  | (addr, (cl, ci, cg)) => ci
  end.

Definition get_ctx_g (ctx : ctx_val) :=
  match ctx with
  | (addr, (cl, ci, cg)) => cg
  end.

Definition get_stk_addr (stk : stack_val) :=
  match stk with
  | (addr, _) => addr
  end.

Definition get_stk_cont (stk : stack_val) :=
  match stk with
  | (_, lfp) => lfp
  end.

Inductive stack_frame_constraint' :
  Address -> Word -> FrameList -> list (Frame * Frame) -> Word -> Prop :=
| frame_invalid :
    forall l id F lfp vi,
      post_cwp id = vi -> 
      stack_frame_constraint' l id F lfp vi

| frame_valid :
    forall l id F lfp vi fml fmi fml' fmi',
      post_cwp id <> vi ->
      get_frame_nth fmi 6 = Some l -> 
      stack_frame_constraint' (l -ᵢ ($ 64)) (post_cwp id) F lfp vi ->
      stack_frame_constraint' l id (fml :: fmi :: F) ((fml', fmi') :: lfp) vi.

Definition stack_frame_constraint (stk : stack_val) F id vi :=
  stack_frame_constraint' (get_stk_addr stk) id F (get_stk_cont stk) vi. 

Inductive stack_frame_top : list (Frame * Frame) -> FrameList -> Prop :=
| top_eq :
    forall lfp lfp' fml fmi F F',
      lfp = (fml, fmi) :: lfp' -> F = fml :: fmi :: F' ->
      stack_frame_top lfp F.

Inductive stack_frame_save' : Word -> FrameList -> list (Frame * Frame) -> Word -> Prop :=
| frame_save_end :
    forall id lfp F vi,
      id = vi ->
      stack_frame_save' id F lfp vi

| frame_save_cons :
    forall id lfp lfp' F F' fml fmi vi,
      id <> vi -> lfp = (fml, fmi) :: lfp' -> F = fml :: fmi :: F' ->
      stack_frame_save' (post_cwp id) F' lfp' vi ->
      stack_frame_save' id F lfp vi.

Definition stack_frame_save F (stk : stack_val) id vi :=
  let (sa, lfp) := stk in
  stack_frame_save' id F lfp vi.

Definition ctx_win_match (ctx : ctx_val) (fml fmi fmg : Frame) (vy : Word) :=
  match ctx with
  | (ca, (cl, ci, cg, cy)) =>
    cl = get_list_pre (frame_to_list fml) 3 /\ ci = frame_to_list fmi /\
    tl cg = tl (frame_to_list fmg) /\ cy = vy
  end.

Definition ctx_win_save (ctx : ctx_val) (fml fmi fmg : Frame) (vy : Word) :=
  ctx_win_match ctx fml fmi fmg vy.

Definition ctx_win_restore (ctx : ctx_val) (fml fmi fmg : Frame) (vy : Word) :=
  ctx_win_match ctx fml fmi fmg vy.

Definition ctx_pt_stk (ctx : ctx_val) (stk : stack_val) : Prop :=
  let lfp := get_stk_cont stk in
  let cri := get_ctx_i ctx in
  let sa := get_stk_addr stk in
  (length lfp >= 1 /\ nth_val 6 cri = Some sa).
  
Definition FrameState (id vi : Word) (F : FrameList) :=
  {| id, F |} ** Rsp Rwim |=> (($ 1) <<ᵢ vi) ** [| length F = 13|] **
  [| ($ 0) <=ᵤᵢ id <=ᵤᵢ ($ 7) /\ ($ 0) <=ᵤᵢ vi <=ᵤᵢ ($ 7) |].

(*+ Specification +*)
Definition os_int_ta0_handler_pre (vl : list logicvar) :=
  EX fmg fmo fml fmi id F vy vi bv ll
     ct cctx cstk nt nctx nstk vz vn,
  [| vl = logic_fm fmg :: logic_fm fml :: logic_fm fmi :: logic_lv id
          :: logic_fmls F :: logic_lv vy :: logic_lv vi :: logic_lv bv :: logic_lv ll
          :: logic_lv ct :: logic_ctx cctx :: logic_stk cstk
          :: logic_lv nt :: logic_ctx nctx :: logic_stk nstk :: nil |] **
  GlobalRegs fmg ** Regs fmo fml fmi ** FrameState id vi F ** Rsp Ry |=> vy **
  z |=> vz ** n |=> vn **
  OSTaskCur |-> ct ** OSTaskNew |-> nt ** OSTaskSwitchFlag |-> bv ** OSIntNestCnt |-> ll **
  context cctx ** stack cstk ** [| get_frame_nth fml 0 = Some id |] **
  (
    [| bv = OSFALSE|] ** Atrue
      \\//
    (
      [| bv = OSTRUE |] **    
      context nctx ** stack nstk **
      [| ct <> ($ 0) -> (get_ctx_addr cctx = ct +ᵢ OS_CONTEXT_OFFSET) |] **
      [| get_ctx_addr nctx = nt +ᵢ OS_CONTEXT_OFFSET /\ ctx_pt_stk nctx nstk |] **
      [| stack_frame_constraint cstk (fml :: fmi :: F ++ (fmo :: nil)) id vi |]
    )
  ).

Definition os_int_ta0_handler_post (vl : list logicvar) :=
  EX fmg fmg' fmo' fml fml' fmi fmi' id id' F F' vy vy' vi vi' bv ll
     ct cctx cctx' cstk cstk' nt nctx nstk vz' vn',
  [| vl = logic_fm fmg :: logic_fm fml :: logic_fm fmi :: logic_lv id
          :: logic_fmls F :: logic_lv vy :: logic_lv vi :: logic_lv bv :: logic_lv ll
          :: logic_lv ct :: logic_ctx cctx :: logic_stk cstk
          :: logic_lv nt :: logic_ctx nctx :: logic_stk nstk :: nil |] **
  GlobalRegs fmg' ** Regs fmo' fml' fmi' ** FrameState id' vi' F' ** Rsp Ry |=> vy' **
  z |=> vz' ** n |=> vn' **
  OSTaskCur |-> ct ** OSTaskNew |-> nt ** OSTaskSwitchFlag |-> OSFALSE ** OSIntNestCnt |-> ll **
  context cctx' ** stack cstk' ** [| get_frame_nth fml' 0 = Some id' |] **
  [| get_ctx_addr cctx = get_ctx_addr cctx' /\ get_stk_addr cstk = get_stk_addr cstk' |] **
  (
    (
      [| bv = OSFALSE /\
         get_global_valid fmg' = get_global_valid fmg /\
         get_local_valid fml' =
         get_local_valid (update_frame (update_frame fml 1 ((get_frame_nth' fml 1) +ᵢ ($ 4))) 2
                             ((get_frame_nth' fml 2) +ᵢ ($ 4))) /\
         fmi' = fmi /\ id' = id /\ vi' = vi /\ F = F' /\
         vy' = vy /\ cctx = cctx' /\ cstk = cstk' |] ** Atrue
    )
      \\//
    (
      [| bv = OSTRUE |] **
      context nctx ** stack nstk **
      [| (get_ctx_addr cctx = ct +ᵢ OS_CONTEXT_OFFSET) ->
         (ctx_pt_stk cctx' cstk' /\ stack_frame_save F cstk' id vi /\
          ctx_win_save cctx (update_frame (update_frame fml 1 ((get_frame_nth' fml 1) +ᵢ ($ 4))) 2
                             ((get_frame_nth' fml 2) +ᵢ ($ 4))) fmi fmg vy) |] **
      [| stack_frame_constraint nstk (fml' :: fmi' :: F' ++ (fmo' :: nil)) id' vi' /\
         ctx_win_restore nctx fml' fmi' fmg' vy' |]
    )
  ).

Definition os_ta0_return_pre (vl : list logicvar) :=
  EX fmg fmo fml fmi F vi id,
  [| vl = logic_fm fmg :: logic_fm fml :: logic_fm fmi :: logic_lv id
          :: logic_fmls F :: logic_lv vi :: nil |] **
  GenRegs (fmg, fmo, fml, fmi) ** FrameState id vi F.

Definition os_ta0_return_post (vl : list logicvar) :=
  EX fmg fmo fml fmi F vi id,
  [| vl = logic_fm fmg :: logic_fm fml :: logic_fm fmi :: logic_lv id
          :: logic_fmls F :: logic_lv vi :: nil |] **
  GenRegs (upd_genreg (fmg, fmo, fml, fmi) l0 id) ** FrameState id vi F.
                                                   
Fixpoint convert_spec (ls : list (Address * Address * fspec)) :
  funspec :=
  match ls with
  | nil => fun _ : Address * Address => None
  | (f1, f2, spec) :: ls' =>
    fun f : Address * Address =>
      let (f1', f2') := f in
      if AddrEq.eq f1 f1' then
        if AddrEq.eq f2 f2' then
          Some spec
        else
          convert_spec ls' f
      else
        convert_spec ls' f
  end.


Definition ta0_window_ok_pre (vl : list logicvar) :=
  EX fmg fmo fml fmi id F vy vi ll
     ct cctx cstk nt nctx nstk vz vn,
  [| vl = logic_fm fmg :: logic_fm fml :: logic_fm fmi :: logic_lv id
          :: logic_fmls F :: logic_lv vy :: logic_lv vi :: logic_lv ll
          :: logic_lv ct :: logic_ctx cctx :: logic_stk cstk
          :: logic_lv nt :: logic_ctx nctx :: logic_stk nstk :: nil |] **
  GlobalRegs fmg ** Regs fmo fml fmi ** FrameState id vi F ** Rsp Ry |=> vy **
  z |=> vz ** n |=> vn **
  OSTaskCur |-> ct ** OSTaskNew |-> nt ** OSTaskSwitchFlag |-> OSTRUE ** OSIntNestCnt |-> ll **
  context cctx ** stack cstk ** [| get_frame_nth fml 0 = Some id |] ** [| id <> vi |] ** 
  context nctx ** stack nstk **
  [| ct <> ($ 0) -> (get_ctx_addr cctx = ct +ᵢ OS_CONTEXT_OFFSET) |] **
  [| get_ctx_addr nctx = nt +ᵢ OS_CONTEXT_OFFSET /\ ctx_pt_stk nctx nstk |] **
  [| stack_frame_constraint cstk (fml :: fmi :: F ++ (fmo :: nil)) id vi |].

Definition ta0_window_ok_post (vl : list logicvar) :=
  EX fmg fmg' fmo' fml fml' fmi fmi' id id' F F' vy vy' vi vi' ll
     ct cctx cctx' cstk cstk' nt nctx nstk vz' vn',
  [| vl = logic_fm fmg :: logic_fm fml :: logic_fm fmi :: logic_lv id
          :: logic_fmls F :: logic_lv vy :: logic_lv vi :: logic_lv ll
          :: logic_lv ct :: logic_ctx cctx :: logic_stk cstk
          :: logic_lv nt :: logic_ctx nctx :: logic_stk nstk :: nil |] **
  GlobalRegs fmg' ** Regs fmo' fml' fmi' ** FrameState id' vi' F' ** Rsp Ry |=> vy' **
  z |=> vz' ** n |=> vn' **
  OSTaskCur |-> ct ** OSTaskNew |-> nt ** OSTaskSwitchFlag |-> OSFALSE ** OSIntNestCnt |-> ll **
  context cctx' ** stack cstk' ** [| get_frame_nth fml' 0 = Some id' |] **
  [| get_ctx_addr cctx = get_ctx_addr cctx' /\ get_stk_addr cstk = get_stk_addr cstk' |] **
  context nctx ** stack nstk **
  [| (get_ctx_addr cctx = ct +ᵢ OS_CONTEXT_OFFSET) ->
     (ctx_pt_stk cctx' cstk' /\ stack_frame_save F cstk' id vi /\
      ctx_win_save cctx fml fmi fmg vy) |] **
  [| stack_frame_constraint nstk (fml' :: fmi' :: F' ++ (fmo' :: nil)) id' vi' /\
         ctx_win_restore nctx fml' fmi' fmg' vy' |].