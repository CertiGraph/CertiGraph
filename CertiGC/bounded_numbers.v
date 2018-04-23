Require Import ZArith.

Open Local Scope Z.

Definition boundZ (n : nat) : Type := {z : Z | 0 <= z < two_power_nat n}.

(*
Compute boundZ 4.
Program Definition abz : boundZ 4 := exist _ 5 _.
Next Obligation.
  unfold two_power_nat. simpl.
  omega.
Qed.
Compute (proj1_sig abz).
*)

Definition boundZ_Z n : boundZ n -> Z := 
  fun bz => proj1_sig bz.
Coercion boundZ_Z : boundZ >-> Z.

Definition boundN (n : nat) : Type := {j | 0 <= j < 2 ^ n}%nat.
Definition boundN_N n : boundN n -> nat :=
  fun bn => proj1_sig bn.
Coercion boundN_N : boundN >-> nat.

Lemma nexp_zexp: forall n,
  2 ^ Z.of_nat n = Z.of_nat (2^n).
Proof.
  induction n; intros. trivial.
  rewrite Nat2Z.inj_succ.
  simpl Nat.pow.
  rewrite Z.pow_succ_r, Nat2Z.inj_add, plus_0_r, IHn;
  omega.
Qed.

Program Definition boundZ_of_boundN (n : nat) (bn : boundN n) : boundZ n :=
  exist _ (Z.of_nat bn) _.
Next Obligation.
  destruct bn. simpl. rewrite two_power_nat_equiv.
  rewrite nexp_zexp.
  omega.
Qed.
Coercion boundZ_of_boundN : boundN >-> boundZ.

Program Definition boundN_of_boundZ (n : nat) (bz : boundZ n) : boundN n :=
  exist _ (Z.to_nat bz) _.
Next Obligation.
  destruct bz. simpl. rewrite two_power_nat_equiv in a.
  rewrite nexp_zexp in a.
  replace (2 ^ n)%nat with (Z.to_nat (Z.of_nat (2 ^ n))) by apply Nat2Z.id. 
  split. omega.
  apply Z2Nat.inj_lt; omega.
Qed.
Coercion boundN_of_boundZ : boundZ >-> boundN.
