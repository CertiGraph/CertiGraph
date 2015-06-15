Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.
Require Import RamifyCoq.msl_ext.abs_addr.
Require Import RamifyCoq.msl_ext.seplog.
Require Import RamifyCoq.msl_ext.log_normalize.
Require Import RamifyCoq.msl_ext.iter_sepcon.
Require Import RamifyCoq.graph.graph.
Require Import RamifyCoq.graph.graph_reachable.
Require Import Coq.Lists.List.
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
  SGA_COSL: CorableOverlapSepLog SGA_Pred;

  SG_Setting: SpatialGraphSetting;
  trinode : Addr -> Val -> SGA_Pred;
  SGA_MSL: MapstoSepLog AV_SGraph trinode;
  SGA_sMSL: StaticMapstoSepLog AV_SGraph trinode;
  SGA_nMSL: NormalMapstoSepLog AV_SGraph trinode
}.

Global Existing Instances SGA_ND SGA_SL SGA_ClSL SGA_PSL SGA_CoSL SGA_OSL SGA_DSL SGA_COSL SG_Setting SGA_MSL SGA_sMSL SGA_nMSL.

Hint Resolve SGA_ND SGA_SL SGA_ClSL SGA_PSL SGA_CoSL SGA_OSL SGA_DSL SGA_COSL SG_Setting SGA_MSL SGA_sMSL SGA_nMSL.

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
    !!(x = null \/ valid x) && EX l : list Addr, !!reachable_list b_pg x l && iter_sepcon l (graph_cell bm_bi).

  Lemma graph_unfold_null: forall bimg, graph null bimg = emp.
  Proof.
    intros. apply pred_ext; unfold graph.
    + apply andp_left2, exp_left. intros. apply derives_extract_prop. intro. destruct x.
      - simpl. apply derives_refl.
      - exfalso. assert (In a (a :: x)). apply in_eq. rewrite (H a) in H0. apply reachable_head_valid in H0.
        rewrite <- pg_the_same in H0.
        apply valid_not_null in H0. auto.
    + apply andp_right.
      - apply prop_right. left; auto.
      - apply (exp_right nil). simpl. apply andp_right.
        * apply prop_right. intro. split; intro. inversion H. apply reachable_head_valid in H.
          rewrite <- pg_the_same in H. apply valid_not_null in H. exfalso; auto.
        * apply derives_refl.
  Qed.

  (* To be removed *)
  Lemma prop_and {A} {NA: NatDed A}: 
    forall P Q: Prop, prop (P /\ Q) = (prop P && prop Q).
  Proof. intros. apply pred_ext. apply prop_left. intros [? ?]; normalize.
         normalize.
  Qed.

  Lemma graph_unfold_valid:
    forall x bimg d l r, valid x -> gamma bm_bi x = (d, l, r) ->
                         graph x bimg = trinode x (d, l, r) ⊗ graph l bimg ⊗ graph r bimg.
  Proof.
    intros. apply pred_ext.
    + unfold graph. apply andp_left2, exp_left. intro li. normalize_overlap.
      unfold gamma in H0. unfold biEdge in H0. destruct (only_two_neighbours x) as [v1 [v2 ?]].
      inversion H0; subst. clear H0. rewrite <- pg_the_same in H, H1.
      assert (In l (edge_func x)). rewrite e. apply in_eq. rewrite <- pg_the_same in H0.
      destruct (compute_neighbor bm_ma x li H H1 l H0) as [leftL [? ?]].
      assert (In r (edge_func x)). rewrite e. apply in_cons, in_eq. rewrite <- pg_the_same in H4.
      destruct (compute_neighbor bm_ma x li H H1 r H4) as [rightL [? ?]].
      apply (exp_right rightL). normalize_overlap. apply (exp_right leftL). normalize_overlap. apply andp_right.
      - rewrite <- !prop_and. apply prop_right. rewrite <- pg_the_same in *. do 2 (split; auto).
        split; apply (valid_graph x); auto.
      -
  Abort.

End SpatialGraph.
