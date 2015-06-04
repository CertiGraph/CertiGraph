Require Import VST.msl.Extensionality.
Require Import VST.msl.seplog.

Local Open Scope logic.

Class OverlapSL (A: Type) {ND: NatDed A} {SL: SepLog A} := mkOverlapSL {
  ocon: A -> A -> A;
  ocon_emp: forall P, ocon P emp = P;
  ocon_TT: forall P, ocon P TT = P * TT;
  andp_ocon: forall P Q, P && Q |-- ocon P Q;
  sepcon_ocon: forall P Q, P * Q |-- ocon P Q;
  ocon_wand: forall P Q R, (R -* P) * (R -* Q) * R |-- ocon P Q;
  ocon_comm: forall P Q, ocon P Q = ocon Q P;
  ocon_assoc: forall P Q R, ocon (ocon P Q) R = ocon P (ocon Q R);
  ocon_derives: forall P Q P' Q', (P |-- P') -> (Q |-- Q') -> ocon P Q |-- ocon P' Q'
}.

Class ImpredicativeOverlapSL (A: Type) {ND: NatDed A} {SL: SepLog A} {OSL: OverlapSL A} := mkImpredicativeOverlapSL {
  strong_ocon_wand: forall P Q, ocon P Q = EX R : A, (R -* P) * (R -* Q) * R
}.

Instance LiftOverlapSL (A B: Type) {ND: NatDed B} {SL: SepLog B}  {OSL: OverlapSL B}: OverlapSL (A -> B).
  apply (mkOverlapSL (A -> B) _ _ (fun P Q x => ocon (P x) (Q x))).
  + simpl; intros. extensionality x. apply ocon_emp.
  + simpl; intros. extensionality x. apply ocon_TT.
  + simpl; intros. apply andp_ocon.
  + simpl; intros. apply sepcon_ocon.
  + simpl; intros. apply ocon_wand.
  + simpl; intros. extensionality x. apply ocon_comm.
  + simpl; intros. extensionality x. apply ocon_assoc.
  + simpl; intros. apply ocon_derives; auto.
Defined.

Module OconNotation.
Notation "P ⊗ Q" := (ocon P Q) (at level 40, left associativity) : logic.
End OconNotation.

