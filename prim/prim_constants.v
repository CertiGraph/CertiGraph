Require Export VST.floyd.proofauto.

Definition size := 8 : Z.
Definition inf := 2147483646 : Z.
(* Int.max_signed - 1 *)

Lemma size_eq: size = 8.
Proof. auto. Qed.

Lemma inf_eq: inf = 2147483646. 
Proof. auto. Qed.

Lemma size_rep': 0 < size <= Int.max_signed.
Proof. compute; split; [trivial | inversion 1]. Qed.

Lemma size_rep: 0 <= size <= Int.max_signed.
Proof. pose proof size_rep'. lia. Qed.

Lemma inf_rep: 0 <= inf <= Int.max_signed.
Proof. compute; split; inversion 1. Qed.

Lemma inf_repable: repable_signed inf.
Proof.
  unfold repable_signed. rewrite inf_eq.
  compute; split; inversion 1.
Qed.

Global Opaque size.
Global Opaque inf.
