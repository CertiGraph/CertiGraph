Require Import compcert.lib.Integers.
Require Import Coq.ZArith.ZArith.
Local Open Scope Z_scope.

Definition SIZE := 8.
Definition inf := Int.max_signed - Int.max_signed / SIZE.
