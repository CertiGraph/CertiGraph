Require Import VST.msl.Extensionality.
Require Import VST.msl.sepalg.
Require Import RamifyCoq.msl_ext.abs_addr.
Require Import RamifyCoq.msl_ext.ramify_tactics.

Set Implicit Arguments.

Lemma join_identity{A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{CA: Canc_alg A}:
  forall a b c, join a b c -> identity a -> identity b -> identity c.
Proof.
  intros.
  hnf; intros x y ?.
  try_join b x bx.
  apply H1 in H3.
  apply H0 in H4.
  subst; auto.
Qed.

(*

Class Mem_alg (AV: AbsAddr) (A: Type) {J: Join A} {SA: Sep_alg A} := mkMem_alg { 
  exact_mem: A -> Addr -> Val -> Prop;
  joins_no_conflict: forall {a1 a2 p1 p2 v1 v2},
     exact_mem a1 p1 v1 -> exact_mem a2 p2 v2 -> joins a1 a2 -> addr_conflict p1 p2 = true -> False;
  addr_uniq: forall a p1 p2 v1 v2, exact_mem a p1 v1 -> exact_mem a p2 v2 -> p1 = p2;
  mem_uniq: forall a1 a2 a p v1 v2, exact_mem a1 p v1 -> exact_mem a2 p v2 -> join_sub a1 a -> join_sub a2 a -> join a a a
}.

Implicit Arguments Mem_alg [[J][SA]].
Implicit Arguments mkMem_alg [[AV] [A] [J] [SA]].

Lemma exact_mem_non_unit: forall (AV: AbsAddr) {ANE: AddrNonEmpty AV} (A: Type) {J: Join A} {SA: Sep_alg A} {MA: Mem_alg AV A} a p v, exact_mem a p v -> unit_for a a -> False.
Proof.
  intros.
  unfold unit_for in H0.
  assert (joins a a) by eauto.
  eapply joins_no_conflict; eauto.
Qed.

Lemma exact_mem_alignable: forall (AV: AbsAddr) {Al: Alignable AV} (A: Type) {J: Join A} {SA: Sep_alg A} {MA: Mem_alg AV A} a a1 a2 p v1 v2, exact_mem a1 p v1 -> exact_mem a2 p v2 -> join_sub a a1 -> join_sub a a2 -> unit_for a a1 /\ unit_for a a2.
Proof.
  intros.
  
*)