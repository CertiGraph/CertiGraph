Require Import VST.msl.Extensionality.
Require Import VST.msl.seplog.

Local Open Scope logic.

Class HONatDed (A: Type) {ND: NatDed A} := mkHONatDed {
  allp_uncurry: forall (S T: Type) (P: S -> T -> A),
    allp (fun s => allp (P s)) = allp (fun st => P (fst st) (snd st));
  allp_curry: forall (S T: Type) (P: S * T -> A),
    allp P = allp (fun s => allp (fun t => P (s, t)));
  exp_uncurry: forall (S T: Type) (P: S -> T -> A),
    exp (fun s => exp (P s)) = exp (fun st => P (fst st) (snd st));
  exp_curry: forall (S T: Type) (P: S * T -> A),
    exp P = exp (fun s => exp (fun t => P (s, t)));
  allp_exp: forall (S T: Type) (P: S -> T -> A),
    allp (fun s => exp (P s)) = exp (fun t: S -> T => allp (fun s => P s (t s)));
  exp_allp: forall (S T: Type) (P: S -> T -> A),
    exp (fun s => allp (P s)) |-- allp (fun t => exp (fun s => P s t))
}.

Class PreciseSepLog (A: Type) {ND: NatDed A} {SL: SepLog A} := mkPreciseSepLog {
  precise: A -> Prop;
  precise_sepcon_andp_sepcon: forall P Q R, precise P -> (P * Q) && (P * R) |-- P * (Q && R);
  precise_sepcon_cancel: forall P Q R, precise P -> P * Q |-- P * R -> Q |-- R;
  derives_precise: forall P Q, (P |-- Q) -> precise Q -> precise P;
  precise_emp: precise emp;
  precise_sepcon: forall P Q, precise Q -> precise P -> precise (P * Q)
}.

Class MapstoSepLog (Adr Val A: Type) {ND: NatDed A} {SL: SepLog A} {PSL: PreciseSepLog A} := mkMapstoSepLog {
  mapsto: Adr -> Val -> A;
  mapsto_conflict: forall a b b', mapsto a b * mapsto a b' |-- FF;
  mapsto_precise: forall a b, precise (mapsto a b);
  mapsto__precise: forall a, precise (EX b: Val, mapsto a b)
}.

Definition mapsto_ {Adr Val A: Type} {ND: NatDed A} {SL: SepLog A} {PSL: PreciseSepLog A} {MSL: MapstoSepLog Adr Val A} (a: Adr): A := EX b: Val, mapsto a b.

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

Instance LiftOverlapSL (A B: Type) {ND: NatDed B} {SL: SepLog B} {OSL: OverlapSL B}: OverlapSL (A -> B).
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

