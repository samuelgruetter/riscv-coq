Require Import bbv.Word.
Require Import riscv.RiscvBitWidths.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.Numbers.BinNums.
Local Open Scope positive.

Section Riscv.

  Context {B: RiscvBitWidths}.

  (** Import positive numbers as bits with Eq and Ord *)
  Notation Reg := PositiveOrderedTypeBits.t.

  Inductive Register: Set :=
    | RegO: Register
    | RegS: Reg -> Register.

  Inductive Instruction: Set :=
    | Addi(rd: Register)(rs1: Register)(imm12: word wimm): Instruction
    | Slti(rd: Register)(rs1: Register)(imm12: word wimm): Instruction
    | Sltiu(rd: Register)(rs1: Register)(imm12: word wimm): Instruction
    | Andi(rd: Register)(rs1: Register)(imm12: word wimm): Instruction
    | Ori(rd: Register)(rs1: Register)(imm12: word wimm): Instruction
    | Xori(rd: Register)(rs1: Register)(imm12: word wimm): Instruction
    | Slli(rd: Register)(rs1: Register)(shamt: word log2wXLEN): Instruction
    | Srli(rd: Register)(rs1: Register)(shamt: word log2wXLEN): Instruction
(*  | Srai(rd: Register)(rs1: Register)(shamt: word log2wXLEN): Instruction *)
    | Lui(rd: Register)(imm20: word wupper): Instruction
    | Add(rd: Register)(rs1: Register)(rs2: Register): Instruction
    | Sub(rd: Register)(rs1: Register)(rs2: Register): Instruction
    | And(rd: Register)(rs1: Register)(rs2: Register): Instruction
    | Or(rd: Register)(rs1: Register)(rs2: Register): Instruction
    | Xor(rd: Register)(rs1: Register)(rs2: Register): Instruction
    | Mul(rd: Register)(rs1: Register)(rs2: Register): Instruction
    | Slt(rd: Register)(rs1: Register)(rs2: Register): Instruction
    | Sltu(rd: Register)(rs1: Register)(rs2: Register): Instruction
    | Beq(rs1: Register)(rs2: Register)(sbimm12: word wimm): Instruction
    | Bne(rs1: Register)(rs2: Register)(sbimm12: word wimm): Instruction
    | Blt(rs1: Register)(rs2: Register)(sbimm12: word wimm): Instruction
    | Bltu(rs1: Register)(rs2: Register)(sbimm12: word wimm): Instruction
    | Bge(rs1: Register)(rs2: Register)(sbimm12: word wimm): Instruction
    | Bgeu(rs1: Register)(rs2: Register)(sbimm12: word wimm): Instruction
    | Jal(rd: Register)(jimm20: word wupper): Instruction.

  Definition Seqz(rd: Register)(rs1: Register) := Sltiu rd rs1 $1.
  Definition Snez(rd: Register)(rs1: Register) := Sltu rd RegO rs1.
  Definition Nop := Addi RegO RegO $0.
  Definition InfiniteJal := Jal RegO (wneg $4).

  Definition decode: word wInstr -> Instruction. Admitted.

End Riscv.
