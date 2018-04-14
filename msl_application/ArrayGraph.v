Require Import Coq.Logic.Classical.
Require Import Coq.Lists.List.
Require Import Coq.Sets.Ensembles.
Require Import Coq.ZArith.ZArith.
Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.
Require Import compcert.lib.Integers.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.Ensembles_ext.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.Relation_ext.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.weak_mark_lemmas.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.graph_gen.
Require Import RamifyCoq.graph.graph_relation.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.reachable_computable.
Require Export RamifyCoq.graph.FiniteGraph.
Require Export RamifyCoq.graph.MathGraph.
Require Export RamifyCoq.graph.LstGraph.
Require Import RamifyCoq.msl_application.UnionFindGraph.

Local Open Scope logic.
Local Open Scope Z_scope.

Instance Z_EqDec : EqDec Z eq. Proof. hnf. intros. apply Z.eq_dec. Defined.

Definition is_null_Z: DecidablePred Z := existT (fun P : Z -> Prop => forall a : Z, {P a} + {~ P a}) (fun x : Z => x < 0) (fun a : Z => Z_lt_dec a 0).

Definition Graph := (@Graph Z Z _ _ is_null_Z id nat unit unit).
Definition LGraph := (@LGraph Z Z _ _ nat unit unit).
Definition UGraph_LGraph (G: Graph): LGraph := lg_gg G.

Local Coercion UGraph_LGraph: Graph >-> LGraph.
Local Identity Coercion ULGraph_LGraph: LGraph >-> UnionFindGraph.LGraph.
Local Identity Coercion LGraph_LabeledGraph: UnionFindGraph.LGraph >-> LabeledGraph.
Local Coercion pg_lg: LabeledGraph >-> PreGraph.

Instance maGraph(G: Graph): MathGraph G is_null_Z := maGraph G.
Instance finGraph (G: Graph): FiniteGraph G := finGraph G.
Instance liGraph (G: Graph):  LstGraph G id := liGraph G.

Definition vgamma := (@vgamma Z Z _ _ is_null_Z id nat unit unit).
Definition Graph_gen_redirect_parent (g: Graph) (x: Z) (pa: Z) (H: weak_valid g pa) (Hv: vvalid g x) (Hn: ~ reachable g pa x): Graph :=
    Graph_gen_redirect_parent g x pa H Hv Hn.

Class SpatialArrayGraphAssum (Pred : Type):=
  {
    SGP_ND: NatDed Pred;
    SGP_SL : SepLog Pred;
    SGP_ClSL: ClassicalSep Pred;
    SGP_CoSL: CorableSepLog Pred
  }.

Fixpoint makeSet_discrete_PreGraph (size: nat) : PreGraph Z Z :=
  match size with
  | O => Build_PreGraph Z_EqDec Z_EqDec (fun _ => False) (fun _ => False) (fun _ => -1) (fun _ => -1)
  | S n => pregraph_add_edge (pregraph_add_vertex (makeSet_discrete_PreGraph n) (Z.of_nat n)) (Z.of_nat n) (Z.of_nat n) (-1)
  end.

Lemma makeSet_vvalid: forall size x, vvalid (makeSet_discrete_PreGraph size) x <-> 0 <= x < Z.of_nat size.
Proof.
  induction size; simpl; intros; split; intros.
  - exfalso; auto.
  - destruct H. intuition.
  - unfold addValidFunc in H. rewrite Zpos_P_of_succ_nat, <- Z.add_1_r. destruct H; [rewrite IHsize in H|]; intuition.
  - unfold addValidFunc. rewrite Zpos_P_of_succ_nat, <- Z.add_1_r in H. rewrite IHsize. omega.
Qed.

Lemma makeSet_evalid: forall size e, evalid (makeSet_discrete_PreGraph size) e <-> 0 <= e < Z.of_nat size.
Proof.
  induction size; simpl; intros; split; intros.
  - exfalso. auto.
  - destruct H; intuition.
  - unfold addValidFunc in H. rewrite Zpos_P_of_succ_nat, <- Z.add_1_r. destruct H; [apply IHsize in H | subst e]; intuition.
  - unfold addValidFunc. rewrite Zpos_P_of_succ_nat, <- Z.add_1_r in H. rewrite IHsize. omega.
Qed.

Lemma makeSet_evalid_src: forall size e, evalid (makeSet_discrete_PreGraph size) e -> src (makeSet_discrete_PreGraph size) e = e.
Proof.
  induction size; simpl; intros.
  - exfalso; auto.
  - unfold addValidFunc in H. unfold updateEdgeFunc. destruct (equiv_dec (Z.of_nat size) e).
    + unfold Equivalence.equiv in e0. auto.
    + unfold Equivalence.equiv in c. unfold complement in c. destruct H. 1: apply IHsize; auto. exfalso; intuition.
Qed.

Lemma makeSet_dst: forall size e, dst (makeSet_discrete_PreGraph size) e = -1.
Proof. induction size; simpl; intros; auto. unfold updateEdgeFunc. destruct (equiv_dec (Z.of_nat size) e); auto. Qed.

Definition makeSet_discrete_MathGraph (size: nat) : MathGraph (makeSet_discrete_PreGraph size) is_null_Z.
Proof.
  constructor; intros; [split|].
  - rewrite (makeSet_evalid_src _ _ H). rewrite makeSet_evalid in H. rewrite makeSet_vvalid. auto.
  - left. rewrite makeSet_dst. hnf. rewrite Z.compare_lt_iff. intuition.
  - rewrite makeSet_vvalid in H. hnf in H0. rewrite Z.compare_lt_iff in H0. intuition.
Qed.

Definition makeSet_discrete_LstGraph (size: nat) : LstGraph (makeSet_discrete_PreGraph size) id.
Proof.
  constructor; intros.
  - unfold id. split; intros.
    + destruct H0. apply makeSet_evalid_src in H1. intuition.
    + subst e. split.
      * rewrite makeSet_vvalid, <- makeSet_evalid in H. apply makeSet_evalid_src; auto.
      * rewrite makeSet_vvalid in H. rewrite makeSet_evalid. auto.
  - destruct p as [v p]. destruct H as [[? ?] [? ?]]. simpl in H. subst v. clear H2. destruct p; auto. simpl in H1. destruct H1.
    assert (strong_evalid (makeSet_discrete_PreGraph size) z) by (destruct p; [|destruct H1]; auto). clear H1. destruct H2 as [_ [_ ?]].
    rewrite makeSet_dst in H1. rewrite makeSet_vvalid in H1. exfalso; intuition.
Qed.

Fixpoint makeSet_discrete_list (size: nat) :=
  match size with
  | O => nil
  | S n => Z.of_nat n :: makeSet_discrete_list n
  end.

Lemma makeSet_discrete_list_iff: forall size x, List.In x (makeSet_discrete_list size) <-> 0 <= x < Z.of_nat size.
Proof.
  induction size; intros; simpl; split; intros.
  - exfalso; auto.
  - destruct H; intuition.
  - rewrite Zpos_P_of_succ_nat, <- Z.add_1_r. rewrite IHsize in H. intuition.
  - rewrite Zpos_P_of_succ_nat, <- Z.add_1_r in H. rewrite IHsize. omega.
Qed.

Lemma makeSet_discrete_list_NoDup: forall size, NoDup (makeSet_discrete_list size).
Proof. induction size; simpl; constructor; auto; intro. rewrite makeSet_discrete_list_iff in H. intuition. Qed.

Definition makeSet_discrete_FiniteGraph (size: nat) : FiniteGraph (makeSet_discrete_PreGraph size).
Proof.
  constructor; unfold EnumEnsembles.Enumerable, In; exists (makeSet_discrete_list size); split; intros.
  - apply makeSet_discrete_list_NoDup.
  - rewrite makeSet_discrete_list_iff, makeSet_vvalid. intuition.
  - apply makeSet_discrete_list_NoDup.
  - rewrite makeSet_discrete_list_iff, makeSet_evalid. intuition.
Qed.

Definition makeSet_discrete_sound (size: nat) : @LiMaFin _ _ _ _ is_null_Z id (makeSet_discrete_PreGraph size).
Proof. constructor. exact (makeSet_discrete_LstGraph size). exact (makeSet_discrete_MathGraph size). exact (makeSet_discrete_FiniteGraph size). Qed.

Definition makeSet_discrete_LabeledGraph (size: nat) : LGraph := Build_LabeledGraph _ _ _ (makeSet_discrete_PreGraph size) (fun _ => O) (fun _ => tt) tt.

Definition makeSet_discrete_Graph (size: nat) : Graph := Build_GeneralGraph _ _ _ _ (makeSet_discrete_LabeledGraph size) (makeSet_discrete_sound size).

Class SpatialArrayGraph (Addr: Type) (Pred: Type) := vcell_array_at: Addr -> list (nat * Z) -> Pred.

Existing Instances SGP_ND SGP_SL SGP_ClSL SGP_CoSL.

Fixpoint nat_inc_list (n: nat) : list Z :=
  match n with
  | O => nil
  | S n' => nat_inc_list n' ++ (Z.of_nat n' :: nil)
  end.

Lemma nat_inc_list_in_iff: forall n v, List.In v (nat_inc_list n) <-> 0 <= v < Z.of_nat n.
Proof.
  induction n; intros; [simpl; intuition|]. rewrite Nat2Z.inj_succ. unfold Z.succ. simpl. rewrite in_app_iff.
  assert (0 <= v < Z.of_nat n + 1 <-> 0 <= v < Z.of_nat n \/ v = Z.of_nat n) by omega. rewrite H. clear H. rewrite IHn. simpl. intuition.
Qed.

Lemma nat_inc_list_NoDup: forall n, NoDup (nat_inc_list n).
Proof.
  induction n; simpl; [constructor|]. apply NoDup_app_inv; auto.
  - constructor; auto. constructor.
  - intros. rewrite nat_inc_list_in_iff in H. simpl. omega.
Qed.

Lemma nat_inc_list_length: forall n, length (nat_inc_list n) = n. Proof. induction n; simpl; auto. rewrite app_length. simpl. rewrite IHn. intuition. Qed.

Section SpaceArrayGraph.

  Context {Pred: Type}.

  Context {SAGP: SpatialArrayGraphAssum Pred}.

  Context {Addr: Type}.

  Context {SAG: SpatialArrayGraph Addr Pred}.

  Definition graph_vcell_at (g: Graph) (P: Z -> Prop) (x: Addr) :=
    EX l: list Z, !!(forall v, List.In v l <-> P v) && !! NoDup l && vcell_array_at x (map (fun x => vgamma (lg_gg g) x) l).

  Definition full_graph_at (g: Graph) (x: Addr) :=
    EX n: nat, !!(forall v, 0 <= v < Z.of_nat n <-> vvalid (pg_lg (lg_gg g)) v) && !!(Z.of_nat n <= Int.max_signed / 8) && vcell_array_at x (map (fun x => vgamma (lg_gg g) x) (nat_inc_list n)).

End SpaceArrayGraph.
