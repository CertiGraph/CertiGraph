Require Import VST.msl.seplog.
Require Import RamifyCoq.msl_ext.abs_addr.
Require Import RamifyCoq.msl_ext.seplog.
Require Import RamifyCoq.msl_ext.log_normalize.
Require Import RamifyCoq.msl_ext.iter_sepcon.
Require Import RamifyCoq.graph.graph.
Require Import RamifyCoq.graph.graph_reachable.
Import RamifyCoq.msl_ext.seplog.OconNotation.

Class SpatialGraphSetting: Type := {
  Data: Type;
  addr: Type;
  null: addr;
  addr_eq_dec: forall x y: addr, {x = y} + {x <> y};
  addr_eqb: addr -> addr -> bool := fun x y => if addr_eq_dec x y then true else false
}.

Instance AV_SGraph `{SpatialGraphSetting} : AbsAddr.
  apply (mkAbsAddr addr (Data * addr * addr) (fun x y => addr_eqb x y)); simpl; intros.
  + unfold addr_eqb.
    destruct (addr_eq_dec p1 p2), (addr_eq_dec p2 p1); try congruence.
  + unfold addr_eqb in H0.
    destruct (addr_eq_dec p1 p1); congruence.
Defined.

Instance AddrDec `{SpatialGraphSetting}: EqDec Addr. apply Build_EqDec. intros. apply (addr_eq_dec t1 t2). Defined.

Class SpatialGraphAssum: Type := {
  SGA_Pred: Type;
  SGA_ND: NatDed SGA_Pred;
  SGA_SL : SepLog SGA_Pred;
  SGA_ClSL: ClassicalSep SGA_Pred;
  SGA_PSL : PreciseSepLog SGA_Pred;
  SGA_CoSL: CorableSepLog SGA_Pred;
  SGA_OSL: OverlapSepLog SGA_Pred;
  SGA_DSL : DisjointedSepLog SGA_Pred;

  SG_Setting: SpatialGraphSetting;
  trinode : Addr -> Val -> SGA_Pred;
  SGA_MSL: MapstoSepLog AV_SGraph trinode;
  SGA_sMSL: StaticMapstoSepLog AV_SGraph trinode;
  SGA_nMSL: NormalMapstoSepLog AV_SGraph trinode
}.

Global Existing Instances SGA_ND SGA_SL SGA_ClSL SGA_PSL SGA_CoSL SGA_OSL SGA_DSL SG_Setting SGA_MSL SGA_sMSL SGA_nMSL.

Hint Resolve SGA_ND SGA_SL SGA_ClSL SGA_PSL SGA_CoSL SGA_OSL SGA_DSL SG_Setting SGA_MSL SGA_sMSL SGA_nMSL.

Local Open Scope logic.

Section SpatialGraph.

  Context {SGA : SpatialGraphAssum}.

  Definition graph_cell (bi : BiGraph Addr Data) (v : Addr) : SGA_Pred := trinode v (gamma bi v).

  Lemma precise_graph_cell: forall bi v, precise (graph_cell bi v).
  Proof. intros. unfold graph_cell. destruct (gamma bi v) as [[? ?] ?]. apply mapsto_precise. Qed.

  Lemma sepcon_unique_graph_cell: forall bi, sepcon_unique (graph_cell bi).
  Proof.
    repeat intro. unfold graph_cell. destruct (gamma bi x) as [[? ?] ?]. apply mapsto_conflict.
    simpl. unfold addr_eqb. destruct (addr_eq_dec x x); auto.
  Qed.

  Definition graph (x : Addr) (bimg : BiMathGraph Addr Data null): SGA_Pred :=
    (!!(x = null) && emp) || EX l : list Addr, !!reachable_list b_pg x l && iter_sepcon l (graph_cell bm_bi).

  Lemma graph_unfold:
    forall x bimg,
      graph x bimg = (!!(x = null) && emp) ||
                     EX d:Data, EX l:Addr, EX r:Addr, !!(gamma bm_bi x = (d, l, r) /\ valid x) &&
                                                        (trinode x (d, l, r) ⊗ graph l bimg ⊗ graph r bimg).
  Proof.
    intros. apply pred_ext.
    + unfold graph at 1. apply orp_left.
      - apply orp_right1. apply derives_refl.
      - apply orp_right2. apply exp_left; intro l.
        destruct (gamma bm_bi x) as [[dd ll] rr]. apply (exp_right dd), (exp_right ll), (exp_right rr).
  Abort.

End SpatialGraph.
