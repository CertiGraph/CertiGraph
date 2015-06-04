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

Module OconNotation.
Notation "P ⊗ Q" := (ocon P Q) (at level 40, left associativity) : logic.
End OconNotation.

