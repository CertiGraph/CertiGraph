Require Import CertiGraph.dijkstra.dijkstra_env.

Definition size := 8 : Z.
Definition inf := 1879048192 : Z.
(* Int.max_signed - Int.max_signed/size *)

Lemma size_eq: size = 8%Z.
Proof. auto. Qed.

Lemma inf_eq: inf = 1879048192%Z. 
Proof. auto. Qed.

Lemma inf_eq2: Int.repr inf =
               Int.sub (Int.repr 2147483647)
                       (Int.divs (Int.repr 2147483647) (Int.repr 8)).
Proof.
  rewrite inf_eq. compute. trivial.
Qed.

Opaque size.
Opaque inf.
