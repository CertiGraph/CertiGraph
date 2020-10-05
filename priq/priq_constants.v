Require Import VST.floyd.proofauto.

Definition SIZE := 8.
Definition inf := Int.max_signed - 1.
Instance Z_EqDec : EquivDec.EqDec Z eq.
Proof. hnf. intros. apply Z.eq_dec. Defined.

Lemma inf_eq: inf = 2147483646.
Proof. compute; trivial. Qed.

Lemma inf_eq2: Int.sub (Int.repr 2147483647)
                       (Int.repr 1) = Int.repr inf.
Proof. compute. trivial. Qed.

Lemma SIZE_rep: 0 <= SIZE <= Int.max_signed.
Proof. unfold SIZE. set (i:=Int.max_signed); compute in i; subst i. lia. Qed.

Lemma SIZE_rep': 0 < SIZE <= Int.max_signed.
Proof. unfold SIZE. set (i:=Int.max_signed); compute in i; subst i. lia. Qed.

Lemma inf_rep: 0 <= inf <= Int.max_signed.
Proof. set (i:=Int.max_signed); compute in i; subst i. rewrite inf_eq.
lia. Qed.

Lemma inf_repable:
repable_signed inf.
Proof.
unfold repable_signed, SIZE. rewrite inf_eq.
set (j:=Int.min_signed); compute in j; subst j.
set (j:=Int.max_signed); compute in j; subst j.
lia.
Qed.

Global Opaque inf.
