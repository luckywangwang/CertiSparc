Require Import Coqlib.  
Require Import Maps. 

Require Import Integers.
Open Scope Z_scope.
Import ListNotations.

Set Asymmetric Patterns.

Require Import state. 
Require Import language.

Set Implicit Arguments.
Unset Strict Implicit.

Open Scope nat.

(*+ Assertion Language +*)
(* Syntax of assertion language *)
Inductive asrt : Type :=
| Aemp : asrt
| Amapsto : Address -> Word -> asrt
| Aaexpevl : AddrExp -> Address -> asrt
| Aoexpevl : OpExp -> Word -> asrt
| Areg : RegName -> Word -> asrt
| Aregdly : nat -> SpReg -> Word -> asrt
| Apure : Prop -> asrt
| Aframe : Word -> FrameList -> asrt
| Atrue : asrt
| Afalse : asrt
| Aconj : asrt -> asrt -> asrt
| Adisj : asrt -> asrt -> asrt
| Astar : asrt -> asrt -> asrt
| Aforall (ty : Type) (P : ty -> asrt)
| Aexists (ty : Type) (P : ty -> asrt).

Notation "'[|' P '|]'" := (Apure P) (at level 29, no associativity).
Infix "**" := Astar (at level 30, right associativity).
Infix "//\\" := Aconj (at level 31, right associativity).
Infix "\\//" := Adisj (at level 32, right associativity).
Notation "l |-> v" := (Amapsto l v) (at level 20).
Notation "aexp '==ₓ' addr" := (Aaexpevl aexp addr) (at level 20).
Notation "oexp '==ₑ' v" := (Aoexpevl oexp v) (at level 20).
Notation "rn |=> v" := (Areg rn v) (at level 20).
Notation "n '@' rn |==> v" := (Aregdly n rn v) (at level 20).

Notation "'EX' x , p " :=
  (Aexists (fun x => p))
    (at level 32, x ident, right associativity).
Notation "'EX' x : t , p " :=
  (Aexists (fun x : t => p))
    (at level 32, x ident, right associativity).
Notation "'EX' x .. y , p" :=
  (Aexists (fun x => .. (Aexists (fun y => p)) ..))
    (at level 32, x binder, right associativity).

Notation "'FORALL' x , p " :=
  (Aforall (fun x => p))
    (at level 32, x ident, right associativity).
Notation "'FORALL' x : t , p " :=
  (Aforall (fun x : t => p))
    (at level 32, x ident, right associativity).
Notation "'FORALL' x .. y , p" :=
  (Aforall (fun x => .. (Aforall (fun y => p)) ..))
    (at level 32, x binder, right associativity).

Notation "'{|' id , F '|}'" := (Aframe id F) (at level 20).

Definition getmem (s : State) :=
  match s with
  | (M, Q, D) => M
  end.

Definition getregs (s : State) :=
  match s with
  | (M, (R, F), D) => R
  end.

Definition getdlyls (s : State) :=
  match s with
  | (M, (R, F), D) => D
  end.

Definition getframelst (s : State) :=
  match s with
  | (M, (R, F), D) => F
  end.

Definition regInDlyBuff (rn : RegName) (D : DelayList) :=
  match rn with
  | Rr rr => False
  | Rpsr rst => False
  | Rsp rsp => In rsp (getRegs D)
  end.

Inductive noDup (A : Type) : list A -> Prop :=
| NoDup_nil : noDup nil
| NoDup_cons : forall x l,
    ~ In x l -> noDup l -> noDup (x :: l).

Definition inDlyBuff (d : DelayItem) (D : DelayList) :=
  In d D /\ noDup (getRegs D).

(* $ rn = v hold if the value v locates in memory with address R(rn) *)
Definition regSt (rn : RegName) (v : Word) (s : State) :=
  getmem s = MemMap.set (getregs s rn) (Some v) emp /\
  ~ (regInDlyBuff rn (getdlyls s)).

Fixpoint regdlySt (n : nat) (rsp : SpReg) (v : Word) (s : State) :=
  match n with
  | 0%nat => True
  | (S n')%nat => inDlyBuff (n', rsp, v) (getdlyls s) \/ regdlySt n' rsp v s
  end.

(* S1 S2 can be union if their register state and delaylist are same 
and memory states are disjoint *)
Definition state_union (s1 s2 s : State) :=
  match s1, s2 with
  | (M1, Q1, D1), (M2, Q2, D2) =>
    disjoint M1 M2 /\ s = (merge M1 M2, Q1, D1) /\ Q1 = Q2 /\ D1 = D2
  end.

(* semantics of assertion language *)
Fixpoint sat (s : State) (p : asrt) {struct p} : Prop :=
  match p with
  | Aemp => getmem s = emp
  | Amapsto l v => getmem s = MemMap.set l (Some v) emp
  | Aaexpevl aexp addr => eval_addrexp (getregs s) (getmem s) aexp = Some addr /\
                          word_aligned addr = true
  | Aoexpevl oexp v => eval_opexp (getregs s) (getmem s) oexp = Some v
  | Areg rn v => regSt rn v s
  | Aregdly t rsp v =>
    exists v', getmem s = MemMap.set ((getregs s) rsp) (Some v') emp /\
          (regdlySt t rsp v s \/ regSt rsp v s)
  | Apure p => p
  | Aframe id F => regSt cwp id s /\ getframelst s = F
  | Atrue => True
  | Afalse => False
  | Aconj p1 p2 => sat s p1 /\ sat s p2
  | Adisj p1 p2 => sat s p1 \/ sat s p2
  | Astar p1 p2 =>
    exists s1 s2, state_union s1 s2 s /\ sat s1 p1 /\ sat s2 p2
  | Aforall t p' => forall (x : t), sat s (p' x)
  | Aexists t p' => exists (x : t), sat s (p' x)
  end.

Notation "s '|=' p" := (sat s p) (at level 33, no associativity).
Notation "p ==> q" :=
  (forall s, s |= p -> s |= q)
    (at level 33, right associativity).
Notation "p <==> q" :=
  (forall s, s |= p <-> s |= q)
    (at level 33, right associativity).

(*** Inference Rule *)

Definition OutRegs (fm : Frame) : asrt :=
  match fm with
  | consfm w0 w1 w2 w3 w4 w5 w6 w7 =>
    r8 |=> w0 ** r9 |=> w1 ** r10 |=> w2 ** r11 |=> w3 ** r12 |=> w4 **
       r13 |=> w5 ** r14 |=> w6 ** r15 |=> w7
  end.

Definition LocalRegs (fm : Frame) : asrt :=
  match fm with
  | consfm w0 w1 w2 w3 w4 w5 w6 w7 =>
    r16 |=> w0 ** r17 |=> w1 ** r18 |=> w2 ** r19 |=> w3 ** r20 |=> w4 **
        r21 |=> w5 ** r22 |=> w6 ** r23 |=> w7
  end.

Definition InRegs (fm : Frame) : asrt :=
  match fm with
  | consfm w0 w1 w2 w3 w4 w5 w6 w7 =>
    r24 |=> w0 ** r25 |=> w1 ** r26 |=> w2 ** r27 |=> w3 ** r28 |=> w4 **
        r29 |=> w5 ** r30 |=> w6 ** r31 |=> w7
  end.

Definition Regs (fm1 fm2 fm3 : Frame) : asrt :=
  OutRegs fm1 ** LocalRegs fm2 ** InRegs fm3.

(*+ Well-formed Instruction +*)
Inductive wf_ins : asrt -> ins -> asrt -> Prop :=
| ld_rule : forall p q aexp l v v' (rd : GenReg),
    p ==> aexp ==ₓ l ->
    p ==> l |-> v ** rd |=> v' ** q ->
    wf_ins p (ld aexp rd) (l |-> v ** rd |=> v ** q)

| st_rule : forall p aexp l v v1 (rs : GenReg),
    l |-> v ** rs |=> v1 ** p ==> aexp ==ₓ l ->
    wf_ins (l |-> v ** rs |=> v1 ** p) (st rs aexp)
           (l |-> v1 ** rs |=> v1 ** p)

| add_rule : forall p q oexp (rs rd : GenReg) v1 v2 v,
    p ==> ((Or rs) ==ₑ v1 //\\ oexp ==ₑ v2) ->
    p ==> rd |=> v ** q ->
    wf_ins p (add rs oexp rd) (rd |=> (v1 +ᵢ v2) ** q)

| sub_rule : forall p q oexp (rs rd : GenReg) v1 v2 v,
    p ==> ((Or rs) ==ₑ v1 //\\ oexp ==ₑ v2) ->
    p ==> rd |=> v ** q ->
    wf_ins p (sub rs oexp rd) (rd |=> (v1 -ᵢ v2) ** q)

| subcc_rule : forall p q oexp (r1 r2 : GenReg) v1 v2 v vr vn vz,
    p ==> ((Or r1) ==ₑ v1 //\\ oexp ==ₑ v2) -> v = v1 -ᵢ v2 -> 
    p ==> r2 |=> vr ** n |=> vn ** z |=> vz ** q ->
    wf_ins p (subcc r1 oexp r2)
           (r2 |=> v ** n |=> (get_range 31 31 v) ** z |=> (iszero v) ** q)

| and_rule : forall p q oexp (rs rd : GenReg) v1 v2 v,
    p ==> ((Or rs) ==ₑ v1 //\\ oexp ==ₑ v2) ->
    p ==> rd |=> v ** q ->
    wf_ins p (and rs oexp rd) (rd |=> (v1 &ᵢ v2) ** q)

| andcc_rule : forall p q oexp (r1 r2 : GenReg) v1 v2 v vr vn vz,
    p ==> ((Or r1) ==ₑ v1 //\\ oexp ==ₑ v2) -> v = v1 &ᵢ v2 -> 
    p ==> r2 |=> vr ** n |=> vn ** z |=> vz ** q ->
    wf_ins p (andcc r1 oexp r2)
           (r2 |=> v ** n |=> (get_range 31 31 v) ** z |=> (iszero v) ** q)

| or_rule : forall p q oexp (rs rd : GenReg) v1 v2 v,
    p ==> ((Or rs) ==ₑ v1 //\\ oexp ==ₑ v2) ->
    p ==> rd |=> v ** q ->
    wf_ins p (or rs oexp rd) (rd |=> (v1 |ᵢ v2) ** q)

| nop_rule : forall p q,
    p ==> q ->
    wf_ins p nop q

| rd_rule : forall (rsp : SpReg) v v1 (r1 : GenReg) p,
    wf_ins (rsp |=> v ** r1 |=> v1 ** p) (rd rsp r1)
           (rsp |=> v ** r1 |=> v ** p)

| wr_rule : forall (rsp : SpReg) (rs : GenReg) p v v1 v2 oexp,
    rsp |=> v ** p ==> ((Or rs) ==ₑ v1 //\\ oexp ==ₑ v2) ->
    wf_ins (rsp |=> v ** p) (wr rs oexp rsp) ((3 @ rsp |==> (v1 xor v2)) ** p)

| save_rule : forall p p1 q (rs rd : GenReg) id id' F fm1 fm2 fmo fml fmi v1 v2 v v' oexp,
    p ==> ((Or rs) ==ₑ v1 //\\ oexp ==ₑ v2) ->
    p ==> {| id, F ++ (fm1 :: fm2 :: nil) |} ** (Regs fmo fml fmi) ** p1 ->
    id' = pre_cwp id -> win_masked id' v = false ->
    {| id', fml :: fmi :: F |} ** (Regs fm1 fm2 fmo) ** p1 ==> rd |=> v' ** q ->
    wf_ins (Rwim |=> v ** p) (save rs oexp rd) (Rwim |=> v ** rd |=> v1 +ᵢ v2 ** q)

| restore_rule : forall p p1 q (rs rd : GenReg) id id' F fm1 fm2 fmo fml fmi v1 v2 v v' oexp,
    p ==> ((Or rs) ==ₑ v1 //\\ oexp ==ₑ v2) ->
    p ==> {| id, fm1 :: fm2 :: F |} ** (Regs fmo fml fmi) ** p1 ->
    id' = post_cwp id -> win_masked id' v = false ->
    {| id', F ++ (fmo :: fml :: nil)  |} ** (Regs fmi fm1 fm2) ** p1 ==> rd |=> v' ** q ->
    wf_ins (Rwim |=> v ** p) (restore rs oexp rd) (Rwim |=> v ** rd |=> v1 +ᵢ v2 ** q)
    
| ins_conj_rule : forall p1 p2 q1 q2 i,
    wf_ins p1 i q1 -> wf_ins p2 i q2 ->
    wf_ins (p1 //\\ p2) i (q1 //\\ q2)

| ins_disj_rule : forall p1 p2 q1 q2 i,
    wf_ins p1 i q1 -> wf_ins p2 i q2 ->
    wf_ins (p1 \\// p2) i (q1 \\// q2)

| ins_conseq_rule : forall p p1 q q1 i,
    p ==> p1 -> wf_ins p1 i q1 -> q1 ==> q ->
    wf_ins p i q

| ins_frame_rule : forall p q r i,
    wf_ins p i q ->
    wf_ins (p ** r) i (q ** r).

Notation " '|-' '{{' p '}}' i '{{' q '}}' " := (wf_ins p i q) (at level 50).

(*+ Well-formed Sequence +*)

Inductive logicvar : Type :=
| logic_lv : Word -> logicvar
| logic_llv : list Word -> logicvar
| logic_reg : RegName -> logicvar
| logic_fm : Frame -> logicvar
| logic_fmls : FrameList -> logicvar.

Definition fpre := list logicvar -> asrt.
Definition fpost := list logicvar -> asrt.
Definition fspec : Type := fpre * fpost.
Definition funspec := Word * Word -> option fspec.

(* Delay Time Reduce *) Print asrt.
Fixpoint TimReduce (a : asrt) : asrt :=
  match a with
  | p //\\ q => (TimReduce p) //\\ (TimReduce q)
  | p \\// q => (TimReduce p) \\// (TimReduce q)
  | p ** q => (TimReduce p) ** (TimReduce q)
  | Aforall t p => Aforall (fun x : t => (TimReduce (p x)))
  | Aexists t p => Aexists (fun x : t => (TimReduce (p x)))
  | Aregdly t rsp v =>
    match t with
    | O => rsp |=> v
    | S t' => t' @ rsp |==> v
    end
  | _ => a
  end.
Notation "p ↓" := (TimReduce p) (at level 40).

Fixpoint DlyFrameFree (a : asrt) :=
  match a with
  | t @ rn |==> v => False
  | {| id, F |} => False
  | p //\\ q => DlyFrameFree p /\ DlyFrameFree q
  | p \\// q => DlyFrameFree p /\ DlyFrameFree q
  | p ** q => DlyFrameFree p /\ DlyFrameFree q
  | Aforall t p => forall x : t, DlyFrameFree (p x)
  | Aexists t p => forall x : t, DlyFrameFree (p x)
  | _ => True
  end.

Definition fretSta (p1 p2 : asrt) :=
  forall s s', s |= p1 -> s' |= p2 ->
          (exists v, (getmem s) ((getregs s) r15) = Some v /\
                (getmem s') ((getregs s) r15) = Some v).

Inductive wf_seq : funspec -> asrt -> InsSeq -> asrt -> Prop :=
| seq_rule : forall f i I p p' q Spec,
    |- {{ p ↓ }} i {{ p' }} -> wf_seq Spec p' I q ->
    wf_seq Spec p (f # i ;; I) q

| call_rule : forall f f1 f2 i I p p1 p2 p' q r fp fq (L : list logicvar) v (Spec : funspec),
    Spec (f, f +ᵢ ($ 4)) = Some (fp, fq) ->
    (p ↓) ==> r15 |=> v ** p1 ->
    |- {{ (r15 |=> f1 ** p1) ↓ }} i {{ p2 }} -> p2 ==> ((Or r15) ==ₑ f1) ->
    p2 ==> fp L ** r -> fq L ** r ==> p'-> fq L ==> ((Or r15) ==ₑ f1) -> DlyFrameFree r ->  
    wf_seq Spec p (f1 c> call f ;; f2 c> i ;; I) q

| retl_rule : forall p p' q f1 f2 i Spec,
    |- {{ (p ↓) ↓ }} i {{ p' }} -> p' ==> q -> fretSta ((p ↓) ↓) p' ->
    wf_seq Spec p (f1 r> retl ;; f2 r> i) q

| J1_rule : forall p p1 p' q (r1 : GenReg) f f1 f2 aexp Spec fp fq L v r i,
    (p ↓) ==> aexp ==ₓ f -> Spec (f, f +ᵢ ($ 4)) = Some (fp, fq) ->
    (p ↓) ==> r1 |=> v ** p1 -> |- {{ (r1 |=> f1 ** p1) ↓ }} i {{ p' }} ->
    p' ==> fp L ** r -> fq L ** r ==> q -> DlyFrameFree r ->
    wf_seq Spec p (consJ1 f1 aexp r1 f2 i) q

| J2_rule : forall p p1 p2 q r fp fq L aexp1 aexp2 f1 f1' f2 f2' (r1 r2 : GenReg) v1 v2 Spec,
    (p ↓) ==> (aexp1 ==ₓ f1') -> (p ↓) ==> r1 |=> v1 ** p1 ->
    ((r1 |=> f1 ** p1) ↓) ==> (aexp2 ==ₓ f2') -> ((r1 |=> f1 ** p1) ↓) ==> r2 |=> v2 ** p2 ->
    Spec (f1, f2) = Some (fp, fq) ->
    (r2 |=> f2 ** p2) ↓ ==> fp L ** r -> fq L ** r ==> q -> DlyFrameFree r ->
    wf_seq Spec p (consJ2 f1 aexp1 r1 f2 aexp2 r2) q

| Be_rule : forall p p' q r aexp f1 f2 f bv fp fq L i I Spec,
    (p ↓) ==> (aexp ==ₓ f) -> Spec (f, f +ᵢ ($ 4)) = Some (fp, fq) ->
    |- {{ p ↓ }} i {{ p' }} -> (p ↓) ==> z |=> bv ** Atrue ->
    wf_seq Spec ( p' //\\ [| bv =ᵢ ($ 0) = true |] ) I q ->
    ((bv =ᵢ ($ 0) = false) -> ((p' ==> fp L ** r) /\ (fq L ** r ==> q))) ->
    wf_seq Spec p (f1 e> be aexp ;; f2 e> i ;; I) q

| Bne_rule : forall p p' q r aexp f1 f2 f bv fp fq L i I Spec,
    (p ↓) ==> (aexp ==ₓ f) -> Spec (f, f +ᵢ ($ 4)) = Some (fp, fq) ->
    |- {{ p ↓ }} i {{ p' }} -> (p ↓) ==> z |=> bv ** Atrue ->
    wf_seq Spec ( p' //\\ [| bv =ᵢ ($ 0) = false |] ) I q ->
    ((bv =ᵢ ($ 0) = true) -> ((p' ==> fp L ** r) /\ (fq L ** r ==> q))) ->
    wf_seq Spec p (f1 n> bne aexp ;; f2 n> i ;; I) q

| Seq_conseq_ruel : forall p p1 q q1 I Spec,
    p ==> p1 -> q1 ==> q ->
    wf_seq Spec p1 I q1 ->
    wf_seq Spec p I q

| Ex_intro_rule : forall q I {tp:Type} p Spec,
    (forall x', wf_seq Spec (p x') I q) ->
    wf_seq Spec (EX x : tp, p x) I q.

Notation " Spec '|-' '{{' p '}}' I '{{' q '}}' " :=
  (wf_seq Spec p I q) (at level 55).


(*+ Well-formed Code Heap +*)
Inductive wf_cdhp : funspec -> CodeHeap -> funspec -> Prop :=
| cdhp_rule : forall Spec Spec' C fp fq I,
    (
      forall f1 f2 L,
        Spec' (f1, f2) = Some (fp, fq) ->
        LookupC C f1 f2 I ->
        wf_seq Spec (fp L) I (fq L)
    ) ->
    wf_cdhp Spec C Spec'.
     



    

    