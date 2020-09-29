
Definition size := 8.
Definition inf := 1879048192.
(* Int.max_signed - Int.max_signed/size *)

Lemma size_eq: size = 8.
Proof. auto. Qed.

Lemma inf_eq: inf = 1879048192. 
Proof. auto. Qed.

Opaque size.
Opaque inf.
