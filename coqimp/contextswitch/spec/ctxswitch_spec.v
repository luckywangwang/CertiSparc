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

Require Import code.
Require Import reg_lemma.

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
    forall l id F lfp vi fml fmi F' fml' fmi' lfp',
      post_cwp id <> vi -> F = fml :: fmi :: F' -> lfp = (fml', fmi') :: lfp' ->
      get_frame_nth fmi 6 = Some l -> 
      stack_frame_constraint' (l -ᵢ ($ 64)) (post_cwp id) F' lfp' vi ->
      stack_frame_constraint' l id F lfp vi.

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
    cg = frame_to_list fmg /\ cy = vy
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
  [| ($ 0) <=ᵢ id = true /\ id <=ᵢ ($ 7) = true /\ ($ 0) <=ᵢ vi = true /\ vi <=ᵢ ($ 7) = true |].

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
    [| bv = OSFALSE|]
      \\//
    (
      context nctx ** stack nstk **
      [| ct <> ($ 0) -> (get_ctx_addr cctx = ct +ᵢ OS_CONTEXT_OFFSET) |] **
      [| get_ctx_addr nctx = nt +ᵢ OS_CONTEXT_OFFSET /\ ctx_pt_stk nctx nstk |] **
      [| (get_ctx_addr cctx = ct +ᵢ OS_CONTEXT_OFFSET) ->
         stack_frame_constraint cstk (fml :: fmi :: F ++ (fmo :: nil)) id vi |] **
      [| bv = OSTRUE |]
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
         fmg' = fmg /\ fml' = fml /\ fmi' = fmi /\ id' = id /\ vi' = vi /\ F = F' /\
         vy' = vy /\ cctx = cctx' /\ cstk = cstk' |]
    )
      \\//
    (
      context nctx ** stack nstk **
      [| (get_ctx_addr cctx = ct +ᵢ OS_CONTEXT_OFFSET) ->
         (ctx_pt_stk cctx' cstk' /\ stack_frame_save F cstk' id vi /\
          ctx_win_save cctx fml fmi fmg vy) |] **
      [| stack_frame_constraint nstk (fml' :: fmi' :: F' ++ (fmo' :: nil)) id' vi' /\
         ctx_win_restore nctx fml' fmi' fmg' vy' |] **
      [| bv = OSTRUE |]
    )
  ).