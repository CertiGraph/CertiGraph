Require Import VST.msl.Extensionality.
Require Import RamifyCoq.CertiGC.bounded_numbers.
Require Import ZArith.

Local Open Scope Z.

Lemma two_power_nat_pos: forall n,
  0 < two_power_nat n.
Proof.
  intro. rewrite two_power_nat_equiv. rewrite <- two_p_equiv.
  generalize (two_p_gt_ZERO (Z.of_nat n)); omega.
Qed.

Lemma two_power_nat_nonneg: forall n,
  0 <= two_power_nat n.
Proof. intro. generalize (two_power_nat_pos n). omega. Qed.

Lemma two_power_nat_pos': forall n,
  two_power_nat n > 0.
Proof. intro. generalize (two_power_nat_pos n). omega. Qed.

Lemma two_power_nat_lt: forall n m,
  (n < m)%nat ->
  two_power_nat n < two_power_nat m.
Proof.
  induction n; intros.
  * destruct m. inversion H.
    unfold two_power_nat at 1. simpl.
    rewrite two_power_nat_S.
    generalize (two_power_nat_pos m).
    omega.
  * destruct m. omega.
    assert (n < m)%nat by omega.
    specialize (IHn m H0).
    do 2 rewrite two_power_nat_S. omega.
Qed.

Lemma two_power_nat_le: forall n m,
  (n <= m)%nat ->
  two_power_nat n <= two_power_nat m.
Proof.
  intros.
  assert (n < m \/ n = m)%nat by omega.
  destruct H0. apply two_power_nat_lt in H0. omega.
  subst. reflexivity.
Qed.

Lemma two_power_nat_exp: forall a b,
  two_power_nat (a + b) = two_power_nat a * two_power_nat b.
Proof.
  intros.
  repeat (rewrite two_power_nat_equiv; rewrite <- two_p_equiv).
  rewrite Nat2Z.inj_add, two_p_is_exp; omega.
Qed.

Class tagcode (A : Type) : Type := {
  tag_bitsize : nat;
  tag_encode  : A -> Z;
  tag_decode  : Z -> A;
  tag_encode_range  : forall a, (0 <= tag_encode a < two_power_nat tag_bitsize);
  tag_decode_encode : forall a, tag_decode (tag_encode a) = a
}.
Arguments tag_bitsize [A].
Arguments tag_encode [A].
Arguments tag_decode [A].
Arguments tag_encode_range [A].
Arguments tag_decode_encode [A].

Program Definition tag_boundZ (n : nat) : tagcode (boundZ n) :=
  Build_tagcode (boundZ n) n (fun bz => proj1_sig bz) 
                             (fun i => exist _ (Z.modulo i (two_power_nat n)) (Z_mod_lt _ _ (two_power_nat_pos' _))) _ _.
Next Obligation.
  destruct a. auto.
Qed.
Next Obligation.
  destruct a. simpl. apply exist_ext. rewrite Zmod_small; omega.
Defined.

(* In this version of encoding, we encode A to the left of B *)
Program Definition tag_prod {A} {B} (tcA : tagcode A) (tcB : tagcode B) : tagcode (A * B) :=
  Build_tagcode (A * B) (tag_bitsize tcA + tag_bitsize tcB)
    (fun p => ((tag_encode tcA (fst p)) * two_power_nat (tag_bitsize tcB)) + 
                tag_encode tcB (snd p))
    (fun i => (tag_decode tcA (i  /  two_power_nat (tag_bitsize tcB)), 
               tag_decode tcB (i mod two_power_nat (tag_bitsize tcB)))) _ _.
Next Obligation.
  simpl.
  generalize (tag_encode_range tcA a). generalize (tag_encode_range tcB b).
  remember (tag_encode tcA a). remember (tag_encode tcB b).
  remember (tag_bitsize tcA). remember (tag_bitsize tcB). clear.
  split.
  + change 0 with (0 * two_power_nat n0 + 0).
    apply Zplus_le_compat.
    apply Zmult_le_compat_r.
    tauto. 
    apply two_power_nat_nonneg.
    tauto.
  + rewrite two_power_nat_exp.
    replace (two_power_nat n * two_power_nat n0) with
            (((two_power_nat n) - 1) * two_power_nat n0 + two_power_nat n0)
             by ring.
    apply Zplus_le_lt_compat.
    apply Zmult_le_compat; omega.
    tauto.
Qed.
Next Obligation.
  intros. generalize (two_power_nat_pos (tag_bitsize tcB)); intro.
  simpl. f_equal.
  + rewrite Z.add_comm, Z_div_plus_full, Zdiv_small, Z.add_0_l.
    apply tag_decode_encode.
    apply tag_encode_range.
    omega.
  + rewrite Zplus_mod, Z_mod_mult, Z.add_0_l, Z.mod_mod, Zmod_small.
    apply tag_decode_encode.
    apply tag_encode_range.
    omega.
Qed.

Class section_retraction (A B : Type) : Type := {
  sr_f : A -> B;
  sr_g : B -> A;
  sr_eq : forall b, sr_f (sr_g b) = b
}.

Program Definition tag_section_retraction {A B} (tcA: tagcode A) (srAB : section_retraction A B) : tagcode B :=
  Build_tagcode B (tag_bitsize tcA) (fun b => tag_encode tcA (sr_g b)) 
                                    (fun z => sr_f (tag_decode tcA z)) _ _.
Next Obligation.
  apply tag_encode_range.
Qed.
Next Obligation.
  rewrite tag_decode_encode.
  apply sr_eq.
Qed.

Program Definition sr_unit_boundZ (n : nat) : section_retraction (boundZ n) unit :=
  Build_section_retraction (boundZ n) unit 
    (fun _ => tt)
    (fun _ => 0) _.
Next Obligation.
  generalize (two_power_nat_pos n).
  omega.
Qed.
Next Obligation.
  destruct b.
  trivial.
Qed.

Definition tag_unit (n : nat) : tagcode unit := 
  tag_section_retraction (tag_boundZ n) (sr_unit_boundZ n).

(*
Definition 

  apply exist_ext.
Lemma two_power_nat_pos: forall n,
  0 < two_power_nat n.
*)

Program Definition sr_bool_boundZ : section_retraction bool (boundZ 1) :=
  Build_section_retraction bool (boundZ 1) 
    (fun b => if b then 1 else 0) 
    (fun z => if Z.eq_dec z 1 then true else false) _.
Next Obligation.
  unfold two_power_nat. simpl. omega.
Qed.
Next Obligation.
  unfold two_power_nat. simpl. omega.
Qed.
Next Obligation.
  destruct b; case Z.eq_dec; simpl; repeat intro.
  subst. apply exist_ext. trivial.
  apply exist_ext.
  unfold two_power_nat in a. simpl in a. omega.
Qed.



Program Definition tag_bool : tagcode bool :=
  Build_tagcode bool 1 (fun b => if b then 1 else 0) 
                       (fun i => if Z.eq_dec i 1 then true else false) _ _.
Next Obligation.
  destruct a; unfold two_power_nat; simpl; omega.
Qed.
Next Obligation.
  destruct a; auto.
Qed.

Program Definition unit_tc (n : nat) : tagcode unit :=
  Build_tagcode unit n (fun _ => 0) (fun _ => tt) _ _.
Next Obligation.
  generalize (two_power_nat_pos n); omega.
Qed.
Next Obligation.
  destruct a; trivial.
Qed.


Obligation Tactic := intros.

(* In this version of the encoding,  A goes to the right of B *)
Program Definition tag_prodswap {A} {B} (tcB : tagcode B) (tcA : tagcode A) : tagcode (A * B) :=
  let X := tag_prod tcB tcA in
    Build_tagcode (A * B) (tag_bitsize tcA + tag_bitsize tcB) 
                          (fun a => tag_encode X (snd a, fst a)) 
                          (fun i => (snd (tag_decode X i), fst (tag_decode X i))) _ _.
Next Obligation.
  unfold X. rewrite plus_comm. apply tag_encode_range.
Qed.
Next Obligation.
  unfold X. rewrite tag_decode_encode. destruct a. trivial.
Qed.

Program Definition tag_padleft {A} (n : nat) (tcA : tagcode A) : tagcode A :=
  let X := tag_prod (tag_unit n) tcA in
    Build_tagcode A (tag_bitsize X) 
                    (fun a => tag_encode X (tt, a)) 
                    (fun i => snd (tag_decode X i)) _ _.
Next Obligation.
  unfold X. apply tag_encode_range.
Qed.
Next Obligation.
  unfold X. rewrite tag_decode_encode. trivial.
Qed.

Program Definition tag_padright {A} (n : nat) (tcA : tagcode A) : tagcode A :=
  let X := tag_prod tcA (tag_unit n) in
    Build_tagcode A (tag_bitsize X) 
                    (fun a => tag_encode X (a,tt)) 
                    (fun i => fst (tag_decode X i)) _ _.
Next Obligation.
  unfold X. apply tag_encode_range.
Qed.
Next Obligation.
  unfold X. rewrite tag_decode_encode. trivial.
Qed.


Obligation Tactic := Coq.Program.Tactics.program_simpl.

Lemma prod_tag_mod: forall A B (tcA : tagcode A) (tcB: tagcode B) a b, 
  tag_encode (tag_prod tcA tcB) (a,b) mod two_power_nat (tag_bitsize tcB) = tag_encode tcB b.
Proof.
  intros.
  simpl.
  generalize (two_power_nat_pos (tag_bitsize tcB)). intro.
  rewrite Zplus_mod, Z_mod_mult, Z.add_0_l, Z.mod_mod, Zmod_small.
  trivial.
  apply tag_encode_range.
  omega.
Qed.

Lemma prod_tag_div: forall A B (tcA : tagcode A) (tcB: tagcode B) a b,
  tag_encode (tag_prod tcA tcB) (a,b) / two_power_nat (tag_bitsize tcB) = tag_encode tcA a.
Proof.
  intros. simpl.
  rewrite Z.add_comm, Z_div_plus_full, Zdiv_small, Z.add_0_l.
  trivial.
  apply tag_encode_range.
  generalize (two_power_nat_pos (tag_bitsize tcB)).
  omega.
Qed.

