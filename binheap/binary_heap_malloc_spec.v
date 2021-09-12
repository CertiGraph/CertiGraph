Require Import VST.floyd.proofauto.
Require Import CertiGraph.binheap.binary_heap_pro.

(* Axioms for malloc/free -- someday these should be merged to the new verified implementation. *)

Parameter free_tok : val -> Z -> mpred.

Definition mallocN_spec {CS: compspecs} :=
  DECLARE _mallocN
  WITH n: Z
  PRE [tint]
  PROP (4 <= n <= Int.max_unsigned)
  PARAMS (Vint (Int.repr n))
  GLOBALS ()
  SEP ()
  POST [ tptr tvoid ]
  EX v: pointer_val,
  PROP (malloc_compatible n (pointer_val_val v))
  LOCAL (temp ret_temp (pointer_val_val v))
  SEP (data_at_ Tsh (tarray tint (n / sizeof tint)) (pointer_val_val v) *
       free_tok (pointer_val_val v) n).

Definition freeN_spec {CS: compspecs} :=
    DECLARE _freeN
    WITH p: val, n: Z
    PRE [tptr tvoid]
    PROP ()
    PARAMS (p)
    GLOBALS ()
    SEP (data_at_ Tsh (tarray tint n) p;
        free_tok p (sizeof tint * n))
  POST [tvoid]
    PROP () LOCAL () SEP (emp).
