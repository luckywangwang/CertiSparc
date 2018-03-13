Require Import Coqlib.
Require Import Maps.

Require Import Integers.
Open Scope Z_scope.
Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.

(* Word *)
Definition Word := int.

(* Address *)
Definition Address := int.

(*** Definition of Registers **)
(* General Registers *)
Inductive GenReg: Type := 
  | r0: GenReg  | r1: GenReg  | r2: GenReg  | r3: GenReg  | r4: GenReg  | r5: GenReg  | r6: GenReg  | r7: GenReg
  | r8: GenReg  | r9: GenReg  | r10: GenReg | r11: GenReg | r12: GenReg | r13: GenReg | r14: GenReg | r15: GenReg
  | r16: GenReg | r17: GenReg | r18: GenReg | r19: GenReg | r20: GenReg | r21: GenReg | r22: GenReg | r23: GenReg
  | r24: GenReg | r25: GenReg | r26: GenReg | r27: GenReg | r28: GenReg | r29: GenReg | r30: GenReg | r31: GenReg.

(* Auxiliary Registers *)
Inductive AsReg: Type :=
  | asr0: AsReg  | asr1: AsReg  | asr2: AsReg  | asr3: AsReg  | asr4: AsReg  | asr5: AsReg  | asr6: AsReg  | asr7: AsReg
  | asr8: AsReg  | asr9: AsReg  | asr10: AsReg | asr11: AsReg | asr12: AsReg | asr13: AsReg | asr14: AsReg | asr15: AsReg
  | asr16: AsReg | asr17: AsReg | asr18: AsReg | asr19: AsReg | asr20: AsReg | asr21: AsReg | asr22: AsReg | asr23: AsReg
  | asr24: AsReg | asr25: AsReg | asr26: AsReg | asr27: AsReg | asr28: AsReg | asr29: AsReg | asr30: AsReg | asr31: AsReg.

(* PSR *)
Inductive PsrReg: Type :=
| n : PsrReg
| z : PsrReg
| cwp : PsrReg.

(* Special Registers *)
Inductive SpReg: Type :=
| Rwim : SpReg
| Ry : SpReg
| Rasr : AsReg -> SpReg.
Coercion Rasr : AsReg >-> SpReg.

(* Register Name *)
Inductive RegName: Type :=
| Rr : GenReg -> RegName
| Rpsr : PsrReg -> RegName
| Rsp : SpReg -> RegName.
Coercion Rr : GenReg >-> RegName.
Coercion Rpsr : PsrReg >-> RegName.
Coercion Rsp : SpReg >-> RegName.

Lemma RegName_eq: forall (x y : RegName),
    {x = y} + {x <> y}.
Proof.
  repeat decide equality.
Qed.

Module RegNameEq.
  Definition t := RegName.
  Definition eq := RegName_eq.
End RegNameEq.

Module RegMap := EMap(RegNameEq).
Definition RegFile := RegMap.t Address.
 
(*** Window Register  **)
(* Frame *)
Inductive Frame : Type :=
  consfm : Word -> Word -> Word -> Word -> Word -> Word -> Word -> Word -> Frame.
Notation " '[[' w0 , w1 , w2 , w3 , w4 , w5 , w6 , w7 ']]'" :=
  (consfm w0 w1 w2 w3 w4 w5 w6 w7) (at level 200): code_scope.

(* Frame List *)
Definition FrameList : Type := list Frame.

(* RState *)
Definition RState : Type := RegFile * FrameList.

(*** Delay List **)
(* DelayCycle *)
Definition DelayCycle := nat.

(* DelayItem *)
Definition DelayItem : Type := DelayCycle * SpReg * Word.

(* DelayList *)
Definition DelayList : Type := list DelayItem.

(* DelayTime *)
Definition X := 3%nat.

(* set_delay *)
Definition set_delay (rsp : SpReg) (w : Word) (D : DelayList) :=
  (X, rsp, w) :: D.

(* getRegs *)
Fixpoint getRegs (D : DelayList) :=
  match D with
  | (_, rsp, _) :: D' => rsp :: (getRegs D')
  | _ => nil
  end.

(*** Program State **)
(* Operation Expression *)  
Inductive OpExp : Type :=
| Or : GenReg -> OpExp
| Ow : Word -> OpExp.

(* Address Expression *)
Inductive AddrExp : Type :=
| Ao : OpExp -> AddrExp
| Aro : GenReg -> OpExp -> AddrExp.

(* memory *)
Module AddrEq.
  Definition t := Word.
  Definition eq := Int.eq_dec.
End AddrEq.

Module MemMap := EMap(AddrEq).
Definition Memory := MemMap.t (option Word).

(* Some Operations for memory *)
(* disjoint *)
Definition disjoint (M1 : Memory) (M2 : Memory) : Prop :=
  forall (x : Address),
    match M1 x, M2 x with
    | Some _, Some _ => False
    | Some _, None => True
    | None, Some _ => True
    | None, None => True
    end.
Notation "M1 '⊥' M2" := (disjoint M1 M2) (at level 39) : mem_scope.

(* in dom *)
Definition indom (x : Address) (M : Memory) :=
  exists v, M x = Some v.

(* is in dom *)
Definition is_indom (x : Address) (M : Memory) :=
  match M x with
  | Some _ => true
  | None => false
  end.

(* merge *)
Definition merge (M1 : Memory) (M2 : Memory) :=
  fun x => match M1 x with
        | None => M2 x
        | Some b => Some b
        end.
Notation "M1 '⊎' M2" := (merge M1 M2) (at level 39) : mem_scope.

(* emp memory *)
Definition emp : Memory := fun (x : Address) => None. 

(* Label f *)
Definition Label: Type := Word.

(* Program State *)
Definition State: Type := Memory * RState * DelayList.

(*** Expression Evalution *)
Notation "$ n" := (Int.repr n)(at level 1) : code_scope.
Notation "a <<ᵢ b" := (Int.shl a b)(at level 1) : code_scope.
Notation "a >>ᵢ b" := (Int.shru a b)(at level 1) : code_scope.
Notation "a &ᵢ b" := (Int.and a b)(at level 1) : code_scope.
Notation "a |ᵢ b" := (Int.or a b)(at level 1) : code_scope.
Notation "a +ᵢ b" := (Int.add a b)(at level 1) : code_scope.
Notation "a -ᵢ b" := (Int.sub a b)(at level 1) : code_scope.
Notation "a =ᵢ b" := (Int.eq a b)(at level 1) : code_scope.
Notation "a <ᵢ b" := (Int.lt a b)(at level 1) : code_scope.
Notation "a >ᵢ b" := (Int.lt b a)(at level 1) : code_scope.
Notation "a <=ᵢ b" := (orb(Int.lt a b)(Int.eq a b))(at level 1) : code_scope.
Notation "a >=ᵢ b" := (orb(Int.lt b a)(Int.eq a b))(at level 1) : code_scope.
Notation "a !=ᵢ b" := (negb(Int.eq a b))(at level 1) : code_scope.
Notation "a 'modu' b" := (Int.modu a b)(at level 1) : code_scope.
Notation "a 'xor' b" := (Int.xor a b)(at level 1) : code_scope.

Open Scope code_scope.

Definition eval_reg (R : RegFile) (M : Memory) (rn : RegName) :=
  M (R (rn)).

Definition eval_opexp (R : RegFile) (M : Memory) (a : OpExp) :=
  match a with
  | Or r => eval_reg R M r
  | Ow w =>
    if andb (($-4096) <=ᵢ w) (w <=ᵢ ($4095)) then
      Some w
    else
      None
  end.

Definition eval_addrexp (R : RegFile) (M : Memory) (b : AddrExp) :=
  match b with
  | Ao a => eval_opexp R M a
  | Aro r a =>
    match (eval_reg R M r) with
    | Some w1 =>
      match (eval_opexp R M a) with
      | Some w2 => Some (w1 +ᵢ w2)
      | None => None
      end 
    | None => None
    end
  end.

(* set_R set a value in Register *)
Definition set_R (R : RegFile) (M : Memory) (rn : RegName) (w : Word) :=
  if is_indom (R rn) M then
    MemMap.set (R rn) (Some w) M
  else
    M.

(* fetch *) 
Definition fetch_frame (M : Memory) (R : RegFile) (rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 : GenReg) :
  option Frame :=
  match (eval_reg R M rr0), (eval_reg R M rr1), (eval_reg R M rr2), (eval_reg R M rr3), (eval_reg R M rr4), (eval_reg R M rr5), (eval_reg R M rr6), (eval_reg R M rr7) with
  | Some w0, Some w1, Some w2, Some w3, Some w4, Some w5, Some w6, Some w7 =>
    Some ([[w0, w1, w2, w3, w4, w5, w6, w7]])
  | _, _, _, _, _, _, _, _ => None
  end.

Definition fetch (M : Memory) (R : RegFile) :=
  match (fetch_frame M R r8 r9 r10 r11 r12 r13 r14 r15),
        (fetch_frame M R r16 r17 r18 r19 r20 r21 r22 r23),
        (fetch_frame M R r24 r25 r26 r27 r28 r29 r30 r31) with
  | Some fmo, Some fml, Some fmi =>
    Some (fmo :: fml :: fmi :: nil)
  | _, _, _ => None
  end.

(* exe_delay *)
Fixpoint exe_delay (M : Memory) (R : RegFile) (D : DelayList) : Memory * DelayList :=
  match D with
  | (0%nat, rsp, w) :: D =>
    let (M', D') := exe_delay M R D in
    (set_R R M' rsp w, D')
  | (S k, rsp, w) :: D =>
    let (M', D') := exe_delay M R D in
    (M', (k, rsp, w) :: D')
  | nil => (M, D)
  end.



    