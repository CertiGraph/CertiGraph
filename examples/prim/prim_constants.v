Require Import VST.floyd.proofauto.

Definition size := 8 : Z.
Definition inf := 2147483646 : Z.
(* Int.max_signed - 1 *)

Lemma size_eq: size = 8.
Proof. auto. Qed.

Lemma inf_eq: inf = 2147483646. 
Proof. auto. Qed.

Global Opaque size.
Global Opaque inf.
