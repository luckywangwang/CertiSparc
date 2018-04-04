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
Fixpoint stack (l : Address) (lfp : list (Frame * Frame)) :=
  match lfp with
  | (fml, fmi) :: lfp' =>
    stack_frame l fml fmi ** stack (l -ᵢ ($ 64)) lfp'
  | nil => Aemp
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
Definition context (l : Address) (rl ri rg: list Word) (ry : Word) :=
  save_reg l 4 rl ** save_reg (l +ᵢ ($ 16)) 8 ri ** save_reg (l +ᵢ ($ 48)) 8 rg **
  (l +ᵢ ($ 80)) |-> ry.

Definition GlobalRegs (fm : Frame) :=
  match fm with
  | consfm w0 w1 w2 w3 w4 w5 w6 w7 =>
    r0 |=> w0 ** r1 |=> w1 ** r2 |=> w2 ** r3 |=> w3 ** r4 |=> w4 **
       r5 |=> w5 ** r6 |=> w6 ** r7 |=> w7
  end.

Fixpoint nth_val (n : nat) (vl : list Word) {struct vl}:=
  match vl with
    | nil => None
    | v::vl' => match n with
                  | 0 => Some v
                  | S n' => nth_val n' vl'
                end
  end.

Print logicvar. Print logic_llv. 

(*+ Specification +*)
Definition os_int_ta0_handler_pre (vl : list logicvar) :=
  EX fmg fmo fml fmi id F vy vi bv
     ct ct1 crl cri crg cry ctp clfp
     nt nt1 nrl nri nrg nry ntp nlfp,
  [| vl = logic_fmls (fmg :: fmo :: fml :: fmi :: nil) :: logic_lv id :: logic_lv vy
          :: logic_fmls F :: logic_llv (ct :: ct1 :: nil) :: logic_llv (nt :: nt1 :: nil)
          :: logic_llv nrl :: logic_llv nri :: logic_llv nrg :: logic_lv nry
          :: logic_stack nlfp :: logic_lv bv :: nil |] **
  GlobalRegs fmg ** Regs fmo fml fmi ** {| id, F |} ** Rsp Rwim |=> (($ 1) <<ᵢ vi) ** 
  Rsp Ry |=> vy ** OSTaskCur |-> ct ** OSTaskNew |-> nt ** OSTaskSwitchFlag |-> bv **
  context ct1 crl cri crg cry ** context nt1 nrl nri nrg nry **
  stack ctp clfp ** stack ntp nlfp **
  [| bv = OSTRUE \/ bv = OSFALSE |] ** [| length F = 13 |] **
  [| ($ 0) <=ᵢ id /\ id <=ᵢ ($ 7) |] ** [| ($ 0) <=ᵢ vi /\ vi <=ᵢ ($ 7) |] **
  [| (ct <> ($ 0) -> (ct1 = ct +ᵢ OS_CONTEXT_OFFSET)) /\
     (nt <> ($ 0) -> (nt1 = nt +ᵢ OS_CONTEXT_OFFSET)) |] **
  [| nt1 = nt +ᵢ OS_CONTEXT_OFFSET ->
     (length nlfp >= 1 /\ nth_val 6 nri = Some nt1)
  |] **
  [| ct1 = ct +ᵢ OS_CONTEXT_OFFSET ->
     stack_frame_constraint l (fml :: fmi :: F) clfp
  |].

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

