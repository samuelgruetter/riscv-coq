Require Import Coq.omega.Omega.
Require Import bbv.NatLib.

Inductive RiscvBitWidth := Bitwidth32 | Bitwidth64.

Class RiscvBitWidths := bitwidth: RiscvBitWidth.

Notation wXLEN :=
  (match bitwidth with
   | Bitwidth32 => 32
   | Bitwidth64 => 64
   end).

Notation log2wXLEN :=
  (match bitwidth with
   | Bitwidth32 => 5
   | Bitwidth64 => 6
   end).

Notation wXLEN_in_bytes :=
  (match bitwidth with
   | Bitwidth32 => 4
   | Bitwidth64 => 8
   end).
