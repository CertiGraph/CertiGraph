Require Import VST.msl.Extensionality.
Require Import VST.msl.seplog.
Require Import RamifyCoq.msl_ext.abs_addr.

Local Open Scope logic.

Set Implicit Arguments.

Class PreciseSepLog (A: Type) {ND: NatDed A} {SL: SepLog A} := mkPreciseSepLog {
  precise: A -> Prop;
  precise_left_sepcon_andp_distr: forall P P1 P2 Q R, precise P -> P1 |-- P -> P2 |-- P -> (P1 * Q) && (P2 * R) |-- (P1 && P2) * (Q && R);
  derives_precise: forall P Q, (P |-- Q) -> precise Q -> precise P;
  precise_emp: precise emp;
  precise_sepcon: forall P Q, precise Q -> precise P -> precise (P * Q);
  precise_wand_ewand: forall R P Q R', precise P -> R |-- P * (Q -* R') -> Q * (ewand P R) |-- R'
}.

Implicit Arguments PreciseSepLog [[ND] [SL]].
Implicit Arguments mkPreciseSepLog [[A] [ND] [SL]].

Instance LiftPreciseSepLog (A B: Type) {ND: NatDed B} {SL: SepLog B} {PSL: PreciseSepLog B} : PreciseSepLog (A -> B).
  apply (mkPreciseSepLog (fun P => forall a, precise (P a))); simpl; intros.
  + eapply precise_left_sepcon_andp_distr; eauto.
  + eapply derives_precise; eauto.
  + apply precise_emp.
  + apply precise_sepcon; auto.
  + apply precise_wand_ewand; auto.
Defined.

Class MapstoSepLog {Addr Val: Type} (AV: AbsAddr Addr Val) {A: Type} (mapsto: Addr -> Val -> A) {ND: NatDed A} {SL: SepLog A} {PSL: PreciseSepLog A} := mkMapstoSepLog {
  mapsto_: Addr -> A := fun p => EX v: Val, mapsto p v;
  mapsto__precise: forall p, precise (mapsto_ p)
}.

Implicit Arguments MapstoSepLog [[Addr] [Val] [A] [ND] [SL] [PSL]].
Implicit Arguments mkMapstoSepLog [[Addr] [Val] [A] [mapsto] [ND] [SL] [PSL]].

Class OverlapSepLog (A: Type) {ND: NatDed A} {SL: SepLog A} {PSL: PreciseSepLog A}:= mkOverlapSepLog {
  ocon: A -> A -> A;
  owand: A -> A -> A;
  ocon_emp: forall P, ocon P emp = P;
  ocon_TT: forall P, ocon P TT = P * TT;
  andp_ocon: forall P Q, P && Q |-- ocon P Q;
  ocon_andp_prop : forall (P : A) (Q : Prop) (R : A),
      ocon P (!!Q && R) = !!Q && ocon P R;
  sepcon_ocon: forall P Q, P * Q |-- ocon P Q;
  ocon_wand: forall P Q R, (R -* P) * (R -* Q) * R |-- ocon P Q;
  ocon_comm: forall P Q, ocon P Q = ocon Q P;
  ocon_assoc: forall P Q R, ocon (ocon P Q) R = ocon P (ocon Q R);
  ocon_derives: forall P Q P' Q', (P |-- P') -> (Q |-- Q') -> ocon P Q |-- ocon P' Q';
  owand_ocon_adjoint: forall P Q R, (ocon P Q |-- R) <-> (P |-- owand Q R);
  ocon_contain: forall P Q, Q |-- P * TT -> Q |-- ocon P Q;
  precise_ocon_contain: forall P Q, precise P -> Q |-- P * TT -> Q = ocon P Q;
  precise_ocon: forall P Q, precise P -> precise Q -> precise (ocon P Q)
}.

Implicit Arguments OverlapSepLog [[ND] [SL] [PSL]].
Implicit Arguments mkOverlapSepLog [[A] [ND] [SL] [PSL]].

Instance LiftOverlapSepLog (A B: Type) {ND: NatDed B} {SL: SepLog B} {PSL: PreciseSepLog B} {OSL: OverlapSepLog B}: OverlapSepLog (A -> B).
  apply (mkOverlapSepLog (fun P Q x => ocon (P x) (Q x)) (fun P Q x => owand (P x) (Q x))); simpl; intros.
  + extensionality x. apply ocon_emp.
  + extensionality x. apply ocon_TT.
  + apply andp_ocon.
  + extensionality x. apply ocon_andp_prop.
  + apply sepcon_ocon.
  + apply ocon_wand.
  + extensionality x. apply ocon_comm.
  + extensionality x. apply ocon_assoc.
  + apply ocon_derives; auto.
  + split; intros; apply owand_ocon_adjoint; auto.
  + apply ocon_contain; auto.
  + extensionality x. apply precise_ocon_contain; auto.
  + apply precise_ocon; auto.
Defined.

Class DisjointedSepLog (A: Type) {ND: NatDed A} {SL: SepLog A} {PSL: PreciseSepLog A} {OSL: OverlapSepLog A} := mkDisjointedSepLog {
  disjointed: A -> A -> Prop;
  ocon_sepcon: forall P Q, disjointed P Q -> ocon P Q |-- P * Q;
  disj_emp: forall P, disjointed P emp;
  disj_comm: forall P Q, disjointed P Q -> disjointed Q P;
  disj_derives: forall P P' Q Q', P |-- P' -> Q |-- Q' -> disjointed P' Q' -> disjointed P Q;
  disj_ocon_right: forall P Q R, disjointed P Q -> disjointed P R -> disjointed P (ocon Q R)
}.

Implicit Arguments DisjointedSepLog [[ND] [SL] [PSL] [OSL]].
Implicit Arguments mkDisjointedSepLog [[A] [ND] [SL] [PSL] [OSL]].

Instance LiftDisjointedSepLog (A B: Type) {ND: NatDed B} {SL: SepLog B} {PSL: PreciseSepLog B} {OSL: OverlapSepLog B} {DSL: DisjointedSepLog B}: DisjointedSepLog (A -> B).
  apply (mkDisjointedSepLog (fun P Q => forall x, disjointed (P x) (Q x))); simpl; intros.
  + apply ocon_sepcon; auto.
  + apply disj_emp.
  + apply disj_comm. apply H.
  + eapply disj_derives; eauto.
  + apply disj_ocon_right; auto.
Defined.

Class StaticMapstoSepLog {Addr Val: Type} (AV: AbsAddr Addr Val) {A: Type} (mapsto: Addr -> Val -> A) {ND: NatDed A} {SL: SepLog A} {PSL: PreciseSepLog A} {MSL: MapstoSepLog AV mapsto} {OSL: OverlapSepLog A} {DSL: DisjointedSepLog A} := mkStaticMapstoSepLog {
  empty_mapsto_emp: forall p v, addr_empty p -> mapsto p v |-- emp;
  mapsto_conflict: forall p1 p2 v1 v2, addr_conflict p1 p2 = true -> mapsto p1 v1 * mapsto p2 v2 |-- FF;
  disj_mapsto_: forall p1 p2, addr_conflict p1 p2 = false -> disjointed (mapsto_ p1) (mapsto_ p2)
}.

Implicit Arguments StaticMapstoSepLog [[Addr] [Val] [A] [ND] [SL] [PSL] [MSL] [OSL] [DSL]].
Implicit Arguments mkStaticMapstoSepLog [[Addr] [Val] [A] [mapsto] [ND] [SL] [PSL] [MSL] [OSL] [DSL]].

Class NormalMapstoSepLog {Addr Val: Type} (AV: AbsAddr Addr Val) {A: Type} (mapsto: Addr -> Val -> A) {ND: NatDed A} {SL: SepLog A} {PSL: PreciseSepLog A} {MSL: MapstoSepLog AV mapsto} {OSL: OverlapSepLog A} {DSL: DisjointedSepLog A} := mkNormalMapstoSepLog {
  mapsto_inj: forall p v1 v2, mapsto p v1 && mapsto p v2 |-- !! (v1 = v2)
}.

Implicit Arguments NormalMapstoSepLog [[Addr] [Val] [A] [ND] [SL] [PSL] [MSL] [OSL] [DSL]].
Implicit Arguments mkNormalMapstoSepLog [[Addr] [Val] [A] [mapsto] [ND] [SL] [PSL] [MSL] [OSL] [DSL]].

Class CorableOverlapSepLog (A: Type) {ND: NatDed A}{SL: SepLog A}{PSL: PreciseSepLog A}{OSL: OverlapSepLog A}{CoSL: CorableSepLog A} := mkCorableOverlapSepLog {
  corable_ocon: forall P Q, corable P -> corable Q -> corable (ocon P Q);
  corable_andp_ocon1: forall P Q R, corable P -> ocon (P && Q) R = P && (ocon Q R)
}.

Implicit Arguments CorableOverlapSepLog [[ND] [SL] [PSL] [OSL] [CoSL]].
Implicit Arguments mkCorableOverlapSepLog [[A] [ND] [SL] [PSL] [OSL] [CoSL]].

Instance LiftCorableOverlapSepLog (A: Type) (B: Type) {NB: NatDed B} {SB: SepLog B} {PSL: PreciseSepLog B} {OSL: OverlapSepLog B} {CoSL: CorableSepLog B} {COSL: CorableOverlapSepLog B}: CorableOverlapSepLog (A -> B).
  apply mkCorableOverlapSepLog; simpl; intros.
  + apply corable_ocon; auto.
  + extensionality x.
    apply corable_andp_ocon1; auto.
Defined.

Class ImpredicativeOSL (A: Type) {ND: NatDed A} {SL: SepLog A} {PSL: PreciseSepLog A} {OSL: OverlapSepLog A} :=
  strong_ocon_wand: forall P Q, ocon P Q = EX R : A, (R -* P) * (R -* Q) * R.

Module OconNotation.
Notation "P ⊗ Q" := (ocon P Q) (at level 40, left associativity) : logic.
End OconNotation.

