Require Import bbv.Word.
Require Import riscv.RiscvBitWidths.
Require Import riscv.Decode.
Require Import Coq.Structures.OrderedTypeEx.

Section Riscv.

  Context {B: RiscvBitWidths}.

  Notation Reg := PositiveOrderedTypeBits.t.

  Class RiscvState(M: Type -> Type) := mkRiscvState {
    getRegister: Register -> M (word wXLEN);
    setRegister: Register -> (word wXLEN) -> M unit;
    loadInst: (word wXLEN) -> M Instruction; (* decode already included *)
    (* not yet:
    loadWord: (word wXLEN) -> M (word wXLEN);
    storeWord: (word wXLEN) -> (word wXLEN) -> M unit;
    *)
    getPC: M (word wXLEN);
    setPC: word wXLEN -> M unit;
  }.

End Riscv.
