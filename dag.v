Require Import msl.msl_classical.
Require Import msl.corec.
Require Import overlapping.
Require Import heap_model.

(* Inductive dag (x:adr) : (pred world) -> Prop := *)
(* | Dag_base: dag x (!!(x = 0) && emp)%pred *)
(* | Dag_ind: forall l r ls rs, dag l ls -> dag r rs -> *)
(*                             dag x (EX d:adr, (mapsto x d) * *)
(*                                              (mapsto (x+1) l) * *)
(*                                              (mapsto (x+2) r) * (ls ⊗ rs))%pred. *)

Definition dagfun (Q: adr -> pred world) (x: adr) :=
  ((!!(x = 0) && emp)
     || (EX d:adr, EX l:adr, EX r:adr, (mapsto x d) *
                                       (mapsto (x+1) l) *
                                       (mapsto (x+2) r) *
                                       ((|> Q l) ⊗ (|> Q r))))%pred.
Lemma dagfun_HOcontractive : HOcontractive dagfun.
Proof.
  apply prove_HOcontractive. intros.
  unfold dagfun.
  apply subp_orp. apply subp_refl.
  apply subp_exp. intro d. apply subp_exp. intro l. apply subp_exp. intro r.
  apply subp_sepcon. apply subp_refl.
  (* * *)
  repeat intro.
  destruct H2 as [x0 [x1 [x2 [x3 [x4 ?]]]]].
  repeat match goal with
           | [H: _ /\ _ |- _] => destruct H
         end.
  destruct (H l x3); generalize (necR_level y a' H1); intro.
  destruct (join_level x3 x2 a' H4); intuition.
  destruct (H r x4); destruct (join_level x0 x1 x3 H2);
  destruct (join_level x1 x2 x4 H3); destruct (join_level x3 x2 a' H4); intuition.
  exists x0, x1, x2, x3, x4.
  repeat (split; auto).
Qed.
Definition dag := HORec dagfun.
