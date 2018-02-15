Require Import Coq.Lists.List.
Import ListNotations.
Require Import riscv.Riscv.
Require Import riscv.RiscvBitWidths32.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.Numbers.BinNums.

Local Open Scope positive.

Definition var: Set := PositiveOrderedTypeBits.t.
Definition Reg: Set := PositiveOrderedTypeBits.t.

Definition var_a: var := 1.
Definition var_b: var := 2.
Definition var_c: var := 3.
Definition var_i: var := 4.

(* stores fib(6) into register var_b (inefficient compiler-generated assembly) *)
Definition fib6_riscv: list Instruction := [
  Addi (RegS 5) RegO $ (1);
  Add (RegS var_a) RegO (RegS 5);
  Addi (RegS 6) RegO $ (2);
  Add (RegS var_b) RegO (RegS 6);
  Addi (RegS 7) RegO $ (1);
  Add (RegS var_i) RegO (RegS 7);
  Add (RegS 8) RegO (RegS var_i);
  Addi (RegS 9) RegO $ (7);
  Sltu (RegS 10) (RegS 8) (RegS 9);
  Beq (RegS 10) RegO ($ (3) ^* $ (14));
  Add (RegS 11) RegO (RegS var_a);
  Add (RegS 12) RegO (RegS var_b);
  Add (RegS 13) (RegS 11) (RegS 12);
  Add (RegS var_c) RegO (RegS 13);
  Add (RegS 14) RegO (RegS var_b);
  Add (RegS var_a) RegO (RegS 14);
  Add (RegS 15) RegO (RegS var_c);
  Add (RegS var_b) RegO (RegS 15);
  Add (RegS 16) RegO (RegS var_i);
  Addi (RegS 17) RegO $ (2);
  Add (RegS 18) (RegS 16) (RegS 17);
  Add (RegS var_i) RegO (RegS 18);
  Jal RegO (^~ ($ (3) ^* $ (18)))
].

Definition initialRiscvMachine(imem: list Instruction): RiscvMachine := {|
  instructionMem := fun (i: word wXLEN) => nth (Nat.div (wordToNat i) 4) imem InfiniteJal;
  registers := fun (r: Reg) => $0;
  pc := $0;
  exceptionHandlerAddr := wneg $4;
|}.

Definition fib6_L_final(fuel: nat): RiscvMachine :=
  execState (run fuel) (initialRiscvMachine fib6_riscv).

Definition fib6_L_res(fuel: nat): word wXLEN :=
  (fib6_L_final fuel).(registers) var_b.

Transparent wlt_dec.

Local Close Scope positive.
Lemma fib6_res_is_13_by_running_it: exists fuel, fib6_L_res fuel = $13.
  exists 200. cbv. reflexivity.
Qed.
