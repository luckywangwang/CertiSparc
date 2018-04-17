Require Import Coqlib.
Require Import Maps.

Require Import Integers.
Open Scope Z_scope.
Import ListNotations. 

Require Import state.

Set Implicit Arguments.
Unset Strict Implicit.

(*+ Syntax of SPARC Code +*)
(* Instructions will not cause control transfermation *)
Inductive ins: Type :=
| ld : AddrExp -> GenReg -> ins
| st : GenReg -> AddrExp -> ins
| nop : ins
| add : GenReg -> OpExp -> GenReg -> ins
| sub : GenReg -> OpExp -> GenReg -> ins
| subcc : GenReg -> OpExp -> GenReg -> ins
| and : GenReg -> OpExp -> GenReg -> ins
| andcc : GenReg -> OpExp -> GenReg -> ins
| or : GenReg -> OpExp -> GenReg -> ins
| sll : GenReg -> OpExp -> GenReg -> ins
| srl : GenReg -> OpExp -> GenReg -> ins
| sett : Word -> GenReg -> ins
| save : GenReg -> OpExp -> GenReg -> ins
| restore : GenReg -> OpExp -> GenReg -> ins
| rd : SpReg -> GenReg -> ins
| wr : GenReg -> OpExp -> SpReg -> ins
| getcwp : GenReg -> ins.

(* Command *)
Inductive command: Type :=
| cntrans : ins -> command
| ccall : Label -> command
| cjumpl : AddrExp -> GenReg -> command
| cretl : command
| cbe : Label -> command
| cbne : Label -> command.

(* Instruction Sequence *)
Inductive InsSeq : Type :=
| consSeq : Label -> ins -> InsSeq -> InsSeq
| consJ1 : Label -> AddrExp -> GenReg ->
       Label -> ins -> InsSeq
| consJ2 : Label -> AddrExp -> GenReg ->
       Label -> AddrExp -> GenReg -> InsSeq
| consCall : Label -> Label -> Label -> ins -> InsSeq -> InsSeq
| consRetl : Label -> Label -> ins -> InsSeq
| consBe : Label -> Label -> Label -> ins -> InsSeq -> InsSeq
| consBne : Label -> Label -> Label -> ins -> InsSeq -> InsSeq.

Notation "f1 # i ;; I" := (consSeq f1 i I) (at level 90, right associativity,
                                              format
                                                "f1 # i ;; '//' I"
                                             ): code_scope.
Notation "f1 > 'jmpl' addr rr ;; f2 > i" := (consJ1 f1 addr rr f2 i)
                                                  (at level 78, right associativity): code_scope.
Notation "f1 >> 'Jmpl' addr1 rr1 ;; f2 >> 'Jmpl' addr2 rr2" :=
  (consJ2 f1 addr1 rr1 f2 addr2 rr2) (at level 78, right associativity): code_scope.
Notation "f1 c> 'call' f ;; f2 c> i ;; I" :=
  (consCall f1 f f2 i I) (at level 90, right associativity,
                                             format
                                             "f1 c> 'call' f ;; f2 c> i ;; '//' I"
                         ): code_scope.
Notation "f1 r> 'retl' ;; f2 r> i" :=
  (consRetl f1 f2 i) (at level 80, right associativity): code_scope.
Notation "f1 e> 'be' addr ;; f2 e> i ;; I" :=
  (consBe f1 addr f2 i I) (at level 90, right associativity,
                           format
                             "f1 e> 'be' addr ;; f2 e> i ;; '//' I"
                          ): code_scope.
Notation "f1 n> 'bne' addr ;; f2 n> i ;; I" :=
  (consBne f1 addr f2 i I) (at level 90, right associativity,
                            format
                              "f1 n> 'bne' addr ;; f2 n> i ;; '//' I"
                           ): code_scope.

(* Test code *)
Definition f1 := ($ 1).
Definition f2 := ($ 2).
Definition f3 := ($ 3).
Definition f4 := ($ 4).

Definition code : InsSeq := 
  consJ1 f3 (Ao (Or r1)) r3 f4 nop. 
Print code.

Definition code1 : InsSeq :=
  consSeq f1 (add r1 (Or r2) r3) (consJ1 f3 (Ao (Or r1)) r3 f4 nop).
Print code1.

Definition code2 : InsSeq :=
  f1 r> retl ;; f2 r> nop.

Definition code3 : InsSeq :=
  f1 # nop ;; f2 # (add r1 (Or r1) r2) ;;
                                       f3 r> retl ;; f4 r> nop.

Definition code4 : InsSeq :=
  f1 c> call f3 ;; f2 c> nop ;; f1 r> retl ;; f2 r> nop.

Open Scope code_scope.

(*+ Code Heap +*)
(* The definition of code heap *)
Definition CodeHeap := MemMap.t (option command). 

(* basic code block constructor *)
Inductive LookupC : CodeHeap -> Label -> Label -> InsSeq -> Prop :=
| lookupNoTransIns :
    forall C f1 f2 I i,
      C f1 = Some (cntrans i) -> LookupC C f2 (f2 +ᵢ ($ 4)) I ->
      LookupC C f1 f2 (f1 # i ;; I)
| lookupJmp1 :
    forall C f1 f2 i aexp rr,
      C f1 = Some (cjumpl aexp rr) ->
      C f2 = Some (cntrans i) ->
      LookupC C f1 f2 (consJ1 f1 aexp rr f2 i)
| lookupJmp2 :
    forall C f1 f2 aexp1 aexp2 rr1 rr2,
      C f1 = Some (cjumpl aexp1 rr1) ->
      C f2 = Some (cjumpl aexp2 rr2) ->
      LookupC C f1 f2 (consJ2 f1 aexp1 rr1 f2 aexp2 rr2)
| lookupRetl :
    forall C f1 f2 i,
      C f1 = Some (cretl) -> C f2 = Some (cntrans i) ->
      LookupC C f1 f2 (f1 r> retl ;; f2 r> i)
| lookupCall :
    forall C f1 f2 f i I,
      C f1 = Some (ccall f) -> C f2 = Some (cntrans i) -> f2 = (f1 +ᵢ ($ 4)) ->
      LookupC C (f2 +ᵢ ($ 4)) (f2 +ᵢ ($ 8)) I ->
      LookupC C f1 f2 (f1 c> call f ;; f2 c> i ;; I)
| lookupBe :
    forall C f1 f2 i I f,
      C f1 = Some (cbe f) -> C f2 = Some (cntrans i) ->
      LookupC C (f2 +ᵢ ($ 4)) (f2 +ᵢ ($ 8)) I ->
      LookupC C f1 f2 (f1 e> be f ;; f2 e> i ;; I)
| lookupBne :
    forall C f1 f2 i I f,
      C f1 = Some (cbne f) -> C f2 = Some (cntrans i) ->
      LookupC C (f2 +ᵢ ($ 4)) (f2 +ᵢ ($ 8)) I ->
      LookupC C f1 f2 (f1 n> bne f ;; f2 n> i ;; I).

(*+ Operational Semantics +*)

Definition get_range: Z -> Z -> Word -> Word :=
  fun i j N =>
    N &ᵢ (((($1)<<ᵢ($(j-i+1))) -ᵢ($1)) <<ᵢ($i)).
Definition word_aligned: Word -> bool :=
  fun w => if (get_range 0 1 w) =ᵢ ($0) then true else false.

Definition iszero v :=
  if Int.eq_dec v ($ 0) then $ 1 else $ 0.

Fixpoint set_Rs R (vl : list (RegName * Word)) :=
  match vl with
  | (rr, w) :: vl =>
    set_Rs (set_R R rr w) vl
  | nil => R
  end.

(* operational Semantics for normal instruction *)
Inductive R__ : Memory * RegFile -> ins -> Memory * RegFile -> Prop :=
| Ld_step : forall aexp (ri : GenReg) M R R' addr v,
    eval_addrexp R aexp = Some addr -> word_aligned addr = true ->
    M addr = Some v -> indom ri R -> set_R R ri v = R' ->
    R__ (M, R) (ld aexp ri) (M, R')

| ST_step : forall (ri : GenReg) aexp M M' R addr v,
    eval_addrexp R aexp = Some addr -> word_aligned addr = true ->
    get_R R ri = Some v -> indom addr M -> MemMap.set addr (Some v) M = M' ->
    R__ (M, R) (st ri aexp) (M', R)

| Nop_step : forall M R,
    R__ (M, R) nop (M, R)

| Add_step : forall M (R R' : RegFile) oexp (rs rd : GenReg) v1 v2,
    get_R R rs = Some v1 -> eval_opexp R oexp = Some v2 ->
    indom rd R -> set_R R rd (v1 +ᵢ v2) = R' ->
    R__ (M, R) (add rs oexp rd) (M, R')
        
| Sub_step : forall M (R R' : RegFile) oexp (rs rd : GenReg) v1 v2,
    get_R R rs = Some v1 -> eval_opexp R oexp = Some v2 ->
    indom rd R -> set_R R rd (v1 -ᵢ v2) = R' ->
    R__ (M, R) (sub rs oexp rd) (M, R')

| Subcc_step : forall M (R R' : RegFile) oexp (rs rd : GenReg) v1 v2 v,
    get_R R rs = Some v1 -> eval_opexp R oexp = Some v2 ->
    indom rd R -> indom n R -> indom z R -> v = v1 -ᵢ v2 ->
    set_Rs R ((Rr rd, v) :: (Rpsr n, get_range 31 31 v) :: (Rpsr z, iszero v) :: nil) = R' ->
    R__ (M, R) (subcc rs oexp rd) (M, R')

| And_step : forall M (R R' : RegFile) oexp (rs rd : GenReg) v1 v2,
    get_R R rs = Some v1 -> eval_opexp R oexp = Some v2 ->
    indom rd R -> set_R R rd (v1 &ᵢ v2) = R' ->
    R__ (M, R) (and rs oexp rd) (M, R')

| Andcc_step : forall M (R R' : RegFile) oexp (rs rd : GenReg) v1 v2 v,
    get_R R rs = Some v1 -> eval_opexp R oexp = Some v2 ->
    indom rd R -> indom n R -> indom z R -> v = v1 &ᵢ v2 ->
    set_Rs R ((Rr rd, v) :: (Rpsr n, get_range 31 31 v) :: (Rpsr z, iszero v) :: nil) = R' ->
    R__ (M, R) (andcc rs oexp rd) (M, R')

| Or_step : forall M (R R' : RegFile) oexp (rs rd : GenReg) v1 v2,
    get_R R rs = Some v1 -> eval_opexp R oexp = Some v2 ->
    indom rd R -> set_R R rd (v1 |ᵢ v2) = R' ->
    R__ (M, R) (or rs oexp rd) (M, R')

| Sll_step : forall M (R R' : RegFile) oexp (rs rd : GenReg) v1 v2,
    get_R R rs = Some v1 -> eval_opexp R oexp = Some v2 ->
    indom rd R -> set_R R rd (v1 <<ᵢ (get_range 0 4 v2)) = R' ->
    R__ (M, R) (sll rs oexp rd) (M, R')

| Srl_step : forall M (R R' : RegFile) oexp (rs rd : GenReg) v1 v2,
    get_R R rs = Some v1 -> eval_opexp R oexp = Some v2 ->
    indom rd R -> set_R R rd (v1 >>ᵢ (get_range 0 4 v2)) = R' ->
    R__ (M, R) (srl rs oexp rd) (M, R')

| Set_step : forall M (R R' : RegFile) (rd : GenReg) w,
    indom rd R -> set_R R rd w = R' ->
    R__ (M, R) (sett w rd) (M, R')

| Rd_step : forall M (R R' : RegFile) (rsp : SpReg) (ri : GenReg) v,
    get_R R rsp = Some v -> indom ri R -> set_R R ri v = R' ->
    R__ (M, R) (rd rsp ri) (M, R')

| GetCwp_step : forall M (R R' : RegFile) (ri : GenReg) v,
    get_R R cwp = Some v -> indom ri R -> set_R R ri v = R' ->
    R__ (M, R) (getcwp ri) (M, R').

(* Operation to write a frame *)
Definition set_frame R (rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 : GenReg) (fm : Frame) :=
  match fm with
  | consfm w0 w1 w2 w3 w4 w5 w6 w7 =>
    set_Rs R
           ((Rr rr0, w0) :: (Rr rr1, w1) :: (Rr rr2, w2) :: (Rr rr3, w3) :: (Rr rr4, w4) ::
                         (Rr rr5, w5) :: (Rr rr6, w6) :: (Rr rr7, w7) :: nil)
  end.

(* Operation to write a window *)
Definition set_window R (fm1 fm2 fm3 : Frame) :=
  let R1 := set_frame R r8 r9 r10 r11 r12 r13 r14 r15 fm1 in
  let R2 := set_frame R1 r16 r17 r18 r19 r20 r21 r22 r23 fm2 in
  set_frame R2 r24 r25 r26 r27 r28 r29 r30 r31 fm3.

Definition N := $ 8.

Definition post_cwp: Word -> Word :=
   fun k => (k +ᵢ ($ 1)) modu N.

Definition pre_cwp: Word -> Word :=
  fun k => (k +ᵢ N -ᵢ ($ 1)) modu N.

Definition win_masked: Word -> Word -> bool :=
  fun w v => if ((($1) <<ᵢ w) &ᵢ v) !=ᵢ ($0) then true else false.

Definition set_spec_reg (rsp : SpReg) (v : Word) :=
  match rsp with
  | Rwim => get_range 0 7 v
  | _ => v
  end.

(* Operations that may touch DelayList and FrameList *)
Inductive Q__: State -> command -> State -> Prop :=
| NormalIns :
    forall i M M' R R' F D,
      R__ (M, R) i (M', R') ->
      Q__ (M, (R, F), D) (cntrans i) (M', (R', F), D)

| SSave :
    forall (M : Memory) (R R' R'': RegFile) D F F' k k' oexp
           fmo fml fmi fm1 fm2 v1 v2 v (rs rd : GenReg),
      get_R R cwp = Some k -> get_R R Rwim = Some v ->
      fetch R = Some [fmo; fml; fmi] -> indom rd R -> 
      get_R R rs = Some v1 -> eval_opexp R oexp = Some v2 -> F = F' ++ (fm1 :: fm2 :: nil) ->
      R' = set_window R fm1 fm2 fmo -> k' = pre_cwp k -> win_masked k' v = false -> 
      R'' = set_Rs R' ((Rpsr cwp, k') :: (Rr rd, v1 +ᵢ v2) :: nil) ->
      Q__ (M, (R, F), D) (cntrans (save rs oexp rd)) (M, (R'', fml :: fmi :: F'), D)

| RRestore :
    forall (M : Memory) (R R' R'': RegFile) D F F' k k' oexp
           fmo fml fmi fm1 fm2 v1 v2 v (rs rd : GenReg),
      get_R R cwp = Some k -> get_R R Rwim = Some v ->
      fetch R = Some [fmo; fml; fmi] -> indom rd R ->
      get_R R rs = Some v1 -> eval_opexp R oexp = Some v2 -> F = fm1 :: fm2 :: F' ->
      R' = set_window R fmi fm1 fm2 -> k' = post_cwp k -> win_masked k' v = false ->
      R'' = set_Rs R' ((Rpsr cwp, post_cwp k) :: (Rr rd, v1 +ᵢ v2) :: nil) ->
      Q__ (M, (R, F), D) (cntrans (restore rs oexp rd)) (M, (R'', F' ++ (fmo :: fml :: nil)), D)

| Wr :
    forall M (R : RegFile) F D D' (rs : GenReg) (rsp : SpReg) oexp v1 v2 v,
      get_R R rs = Some v1 -> eval_opexp R oexp = Some v2 ->
      v = set_spec_reg rsp (v1 xor v2) -> indom rsp R -> D' = set_delay rsp v D ->
      Q__ (M, (R, F), D) (cntrans (wr rs oexp rsp)) (M, (R, F), D').

(* Operation Semantics for Control Transfer *)
Inductive H__ : CodeHeap -> State * Label * Label -> State * Label * Label -> Prop :=
| NTrans :
    forall C i S S' pc npc,
      C pc = Some (cntrans i) -> Q__ S (cntrans i) S' ->
      H__ C (S, pc, npc) (S', npc, (npc +ᵢ ($ 4)))

| Jumpl :
    forall C M aexp rd (R R' : RegFile) F D (pc npc f : Label),
      C pc = Some (cjumpl aexp rd) -> eval_addrexp R aexp = Some f ->
      word_aligned f = true -> indom rd R -> set_R R rd pc = R' ->
      H__ C ((M, (R, F), D), pc, npc) ((M, (R', F), D), npc, f)

| Call :
    forall C M (R R' : RegFile) F D pc npc f,
      C pc = Some (ccall f) -> indom r15 R -> set_R R r15 pc = R' ->
      H__ C ((M, (R, F), D), pc, npc) ((M, (R', F), D), npc, f)

| Retl :
    forall C M (R : RegFile) F D pc npc f,
      C pc = Some (cretl) -> get_R R r15 = Some f ->
      H__ C ((M, (R, F), D), pc, npc) ((M, (R, F), D), npc, f +ᵢ ($ 8))

| Be_true :
    forall C M (R : RegFile) F D pc npc f v,
      C pc = Some (cbe f) -> get_R R z = Some v -> v <> ($ 0) ->
      H__ C ((M, (R, F), D), pc, npc) ((M, (R, F), D), npc, f)

| Be_false :
    forall C M (R : RegFile) F D pc npc f,
      C pc = Some (cbe f) -> get_R R z = Some ($ 0) ->
      H__ C ((M, (R, F), D), pc, npc) ((M, (R, F), D), npc, npc +ᵢ ($ 4))

| Bne_true :
    forall C M (R : RegFile) F D pc npc f,
      C pc = Some (cbne f) -> get_R R z = Some ($ 0) ->
      H__ C ((M, (R, F), D), pc, npc) ((M, (R, F), D), npc, f)

| Bne_false :
    forall C M (R : RegFile) F D pc npc f v,
      C pc = Some (cbne f) -> get_R R z = Some v -> v <> ($ 0) ->
      H__ C ((M, (R, F), D), pc, npc) ((M, (R, F), D), npc, npc +ᵢ ($ 4)).

Inductive P__ : CodeHeap -> State * Label * Label -> State * Label * Label -> Prop :=
  CStep :
    forall C M M' R R' R'' D D' D'' F F' pc pc' npc npc',
      (R', D') = exe_delay R D ->
      H__ C ((M, (R', F), D'), pc, npc) ((M', (R'', F'), D''), pc', npc') ->
      P__ C ((M, (R, F), D), pc, npc) ((M', (R'', F'), D''), pc', npc').