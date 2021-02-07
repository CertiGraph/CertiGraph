Require Import CertiGraph.dijkstra.dijkstra_env.

Definition size := 8 : Z.
Definition inf := 1879048193 : Z.
(* Int.max_signed - Int.max_signed/size + 1 *)

Lemma size_eq: size = 8%Z.
Proof. auto. Qed.

Lemma inf_eq: inf = 1879048193%Z.
Proof. auto. Qed.

Global Opaque size.
Global Opaque inf.
