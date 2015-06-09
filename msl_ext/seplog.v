Require Import VST.msl.Extensionality.
Require Import VST.msl.seplog.
Require Import RamifyCoq.msl_ext.abs_addr.

Local Open Scope logic.

Set Implicit Arguments.

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
  precise_sepcon_cancel_left: forall P Q R, precise P -> P * Q |-- P * R -> Q |-- R;
  derives_precise: forall P Q, (P |-- Q) -> precise Q -> precise P;
  precise_emp: precise emp;
  precise_sepcon: forall P Q, precise Q -> precise P -> precise (P * Q)
}.

Implicit Arguments PreciseSepLog [[ND] [SL]].
Implicit Arguments mkPreciseSepLog [[A] [ND] [SL]].

Instance LiftPreciseSepLog (A B: Type) {ND: NatDed B} {SL: SepLog B} {PSL: PreciseSepLog B} : PreciseSepLog (A -> B).
  apply (mkPreciseSepLog (fun P => forall a, precise (P a))); simpl; intros.
  + apply precise_sepcon_andp_sepcon; auto.
  + eapply precise_sepcon_cancel_left; eauto.
  + eapply derives_precise; eauto.
  + apply precise_emp.
  + apply precise_sepcon; auto.
Defined.

Class MapstoSepLog (AV: AbsAddr) (A: Type) {ND: NatDed A} {SL: SepLog A} {PSL: PreciseSepLog A} := mkMapstoSepLog {
  mapsto: Addr -> Val -> A;
  mapsto_: Addr -> A := fun p => EX v: Val, mapsto p v;
  mapsto__precise: forall p, precise (mapsto_ p);
  mapsto_conflict: forall p1 p2 v1 v2, addr_conflict p1 p2 = true -> mapsto p1 v1 * mapsto p2 v2 |-- FF
}.

Implicit Arguments MapstoSepLog [[ND] [SL] [PSL]].
Implicit Arguments mkMapstoSepLog [[AV] [A] [ND] [SL] [PSL]].

(*
Class NonEmpMapstoSL (AV: AbsAddr) (A: Type) {ND: NatDed A} {SL: SepLog A} {PSL: PreciseSepLog A} {MSL: MapstoSepLog AV A} :=
  mapsto_non_emp: forall a b, mapsto a b && emp |-- FF.

We should just say that, if an address is empty, we cannot load or store on it.
*)
Class OverlapSepLog (A: Type) {ND: NatDed A} {SL: SepLog A} {PSL: PreciseSepLog A}:= mkOverlapSepLog {
  ocon: A -> A -> A;
  owand: A -> A -> A;
  ocon_emp: forall P, ocon P emp = P;
  ocon_TT: forall P, ocon P TT = P * TT;
  andp_ocon: forall P Q, P && Q |-- ocon P Q;
  sepcon_ocon: forall P Q, P * Q |-- ocon P Q;
  ocon_wand: forall P Q R, (R -* P) * (R -* Q) * R |-- ocon P Q;
  ocon_comm: forall P Q, ocon P Q = ocon Q P;
  ocon_assoc: forall P Q R, ocon (ocon P Q) R = ocon P (ocon Q R);
  ocon_derives: forall P Q P' Q', (P |-- P') -> (Q |-- Q') -> ocon P Q |-- ocon P' Q';
  owand_ocon_adjoint: forall P Q R, (ocon P Q |-- R) <-> (P |-- owand Q R);
  precise_ocon_self: forall P, precise P -> ocon P P = P;
  disjointed: A -> A -> Prop := fun P Q => ocon P Q |-- P * Q;
  disj_comm: forall P Q, disjointed P Q -> disjointed Q P;
  disj_ocon_right: forall P Q R, precise P -> disjointed P Q -> disjointed P R -> disjointed P (ocon Q R);
  disj_sepcon_right: forall P Q R, precise P -> disjointed P Q -> disjointed P R -> disjointed P (sepcon Q R)
}.

Implicit Arguments OverlapSepLog [[ND] [SL] [PSL]].
Implicit Arguments mkOverlapSepLog [[A] [ND] [SL] [PSL]].

Class MapstoOverlapSepLog (AV: AbsAddr) (A: Type) {ND: NatDed A} {SL: SepLog A} {PSL: PreciseSepLog A} {MSL: MapstoSepLog AV A} {OSL: OverlapSepLog A} :=
  disj_mapsto: forall p1 p2 v1 v2, addr_conflict p1 p2 = false -> disjointed (mapsto p1 v1) (mapsto p2 v2).

Implicit Arguments MapstoOverlapSepLog [[ND] [SL] [PSL] [MSL] [OSL]].

Class ImpredicativeOSL (A: Type) {ND: NatDed A} {SL: SepLog A} {PSL: PreciseSepLog A} {OSL: OverlapSepLog A} :=
  strong_ocon_wand: forall P Q, ocon P Q = EX R : A, (R -* P) * (R -* Q) * R.

Instance LiftOverlapSepLog (A B: Type) {ND: NatDed B} {SL: SepLog B} {PSL: PreciseSepLog B} {OSL: OverlapSepLog B}: OverlapSepLog (A -> B).
  apply (mkOverlapSepLog (fun P Q x => ocon (P x) (Q x)) (fun P Q x => owand (P x) (Q x))); simpl; intros.
  + extensionality x. apply ocon_emp.
  + extensionality x. apply ocon_TT.
  + apply andp_ocon.
  + apply sepcon_ocon.
  + apply ocon_wand.
  + extensionality x. apply ocon_comm.
  + extensionality x. apply ocon_assoc.
  + apply ocon_derives; auto.
  + split; intros; apply owand_ocon_adjoint; auto.
  + extensionality x. apply precise_ocon_self; auto.
  + apply disj_comm. apply H.
  + apply disj_ocon_right; auto.
    apply H0.
    apply H1.
  + apply disj_sepcon_right; auto.
    apply H0.
    apply H1.
Defined.

Module OconNotation.
Notation "P ⊗ Q" := (ocon P Q) (at level 40, left associativity) : logic.
End OconNotation.

