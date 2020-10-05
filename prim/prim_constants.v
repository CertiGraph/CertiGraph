Require Export VST.floyd.proofauto.

Definition SIZE := 8 : Z.
Definition inf := 2147483646 : Z.
(* Int.max_signed - 1 *)

Lemma SIZE_eq: SIZE = 8.
Proof. auto. Qed.

Lemma inf_eq: inf = 2147483646. 
Proof. auto. Qed.

Lemma SIZE_rep': 0 < SIZE <= Int.max_signed.
Proof. compute; split; [trivial | inversion 1]. Qed.

Lemma SIZE_rep: 0 <= SIZE <= Int.max_signed.
Proof. pose proof SIZE_rep'. lia. Qed.

Lemma inf_rep: 0 <= inf <= Int.max_signed.
Proof. compute; split; inversion 1. Qed.

Lemma inf_repable: repable_signed inf.
Proof.
  unfold repable_signed. rewrite inf_eq.
  compute; split; inversion 1.
Qed.

Global Opaque SIZE.
Global Opaque inf.
