Require Import CertiGraph.dijkstra.dijkstra_env.

Definition size := 8 : Z.
Definition inf := 2147483647 : Z.
(* Int.max_signed *)

Lemma size_eq: size = 8%Z.
Proof. auto. Qed.

Lemma inf_eq: inf = 2147483647%Z.
Proof. auto. Qed.

Global Opaque size.
Global Opaque inf.
