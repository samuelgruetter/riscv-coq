Require Import Coq.ZArith.BinInt.
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

    loadByte: Z -> M (word 8);
    loadHalf: Z -> M (word 16);
    loadWord: Z -> M (word 32);
    loadDouble: Z -> M (word 64);

    storeByte: Z -> (word 8) -> M unit;
    storeHalf: Z -> (word 16) -> M unit;
    storeWord: Z -> (word 32) -> M unit;
    storeDouble: Z -> (word 64) -> M unit;

    getPC: M Z;
    setPC: Z -> M unit;
  }.

(* With word-based addresses:

  Class RiscvState(M: Type -> Type) := mkRiscvState {
    getRegister: Register -> M (word wXLEN);
    setRegister: Register -> (word wXLEN) -> M unit;

    loadByte: (word wXLEN) -> M (word 8);
    loadHalf: (word wXLEN) -> M (word 16);
    loadWord: (word wXLEN) -> M (word 32);
    loadDouble: (word wXLEN) -> M (word 64);

    storeByte: (word wXLEN) -> (word 8) -> M unit;
    storeHalf: (word wXLEN) -> (word 16) -> M unit;
    storeWord: (word wXLEN) -> (word 32) -> M unit;
    storeDouble: (word wXLEN) -> (word 64) -> M unit;

    getPC: M Z;
    setPC: Z -> M unit;
  }.
*)

End Riscv.
