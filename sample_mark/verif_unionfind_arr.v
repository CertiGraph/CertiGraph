Require Import Coq.omega.Omega.
Require Import VST.floyd.proofauto.
Require Import RamifyCoq.sample_mark.env_unionfind_arr.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.graph_relation.
Require Import RamifyCoq.graph.reachable_computable.
Require Import RamifyCoq.graph.UnionFind.
Require Import RamifyCoq.msl_application.ArrayGraph.
Require Import RamifyCoq.floyd_ext.share.
Require Import RamifyCoq.sample_mark.spatial_array_graph.

Local Open Scope logic.

Arguments SingleFrame' {l} {g} {s}.

Local Coercion Graph_LGraph: Graph >-> LGraph.
Local Identity Coercion Graph_GeneralGraph: Graph >-> GeneralGraph.
Local Identity Coercion LGraph_LabeledGraph: LGraph >-> LabeledGraph.
Local Coercion pg_lg: LabeledGraph >-> PreGraph.

Definition mallocN_spec :=
 DECLARE _mallocN
  WITH sh:wshare, n: Z
  PRE [ 67%positive OF tint]
     PROP (4 <= n <= Int.max_unsigned) 
     LOCAL (temp 67%positive (Vint (Int.repr n)))
     SEP ()
  POST [ tptr tvoid ] 
     EX v: pointer_val,
     PROP (malloc_compatible n (pointer_val_val v)) 
     LOCAL (temp ret_temp (pointer_val_val v)) 
     SEP (memory_block sh n (pointer_val_val v)).

Definition whole_graph sh g x := (@full_graph_at mpred SAGA_VST pointer_val (SAG_VST sh) g x).

Definition makeSet_spec :=
  DECLARE _makeSet
  WITH sh: wshare, V: Z
    PRE [_V OF tint]
      PROP (0 < V <= Int.max_signed / 8)
      LOCAL (temp _V (Vint (Int.repr V)))
      SEP ()
    POST [tptr vertex_type]
      EX g: Graph, EX rt: pointer_val,
      PROP (forall i: Z, 0 <= i < V -> vvalid g i)
      LOCAL (temp ret_temp (pointer_val_val rt))
      SEP (whole_graph sh g rt).

Definition find_spec :=
  DECLARE _find
  WITH sh: wshare, g: Graph, subsets: pointer_val, i: Z
    PRE [_subsets OF (tptr vertex_type), _i OF tint]
      PROP (vvalid g i)
      LOCAL (temp _subsets (pointer_val_val subsets); temp _i (Vint (Int.repr i)))
      SEP (whole_graph sh g subsets)
    POST [tint]
      EX g': Graph, EX rt: Z,
      PROP (findS g i g' /\ uf_root g' i rt)
      LOCAL (temp ret_temp (Vint (Int.repr rt)))
      SEP (whole_graph sh g' subsets).

Definition union_spec :=
 DECLARE _Union
  WITH sh: wshare, g: Graph, subsets: pointer_val, x: Z, y: Z
  PRE [ _subsets OF (tptr vertex_type), _x OF tint, _y OF tint]
          PROP  (vvalid g x /\ vvalid g y)
          LOCAL (temp _subsets (pointer_val_val subsets); temp _x (Vint (Int.repr x)); temp _y (Vint (Int.repr x)))
          SEP   (whole_graph sh g subsets)
  POST [ Tvoid ]
        EX g': Graph,
        PROP (uf_union g x y g')
        LOCAL ()
        SEP (whole_graph sh g' subsets).

Definition Vprog : varspecs := nil.

Definition Gprog : funspecs := mallocN_spec :: makeSet_spec :: find_spec :: union_spec ::nil.

Lemma whole_graph_empty: forall sh rt n, 0 <= n -> malloc_compatible n (pointer_val_val rt) -> whole_graph sh (makeSet_discrete_Graph 0) rt = emp.
Proof.
  intros. unfold whole_graph, full_graph_at. simpl. unfold graph_vcell_at. simpl. unfold vgamma. simpl. unfold vcell_array_at. unfold SAG_VST. apply pred_ext.
  - apply exp_left. intro l. Intros. destruct l. 2: exfalso; rewrite <- (H1 z); left; auto. simpl. unfold data_at, field_at. simpl. Intros.
    unfold at_offset. rewrite data_at_rec_eq. simpl. unfold unfold_reptype. simpl. rewrite array_pred_len_0; auto.
  - apply (exp_right nil). simpl. apply andp_right; [apply andp_right|]; [apply prop_right_emp ..|]; [intros; intuition | constructor |].
    unfold data_at. unfold field_at. apply andp_right.
    + apply prop_right_emp. apply malloc_compatible_field_compatible. simpl.
      * unfold malloc_compatible in *. destruct (pointer_val_val rt); auto. destruct H0. split; auto. omega.
      * unfold legal_alignas_type, nested_pred. simpl. auto.
      * unfold legal_cosu_type, nested_pred. simpl. auto.
      * simpl. auto.
      * simpl. exists 2. simpl. auto.
    + unfold at_offset. rewrite data_at_rec_eq. simpl. unfold unfold_reptype. simpl. rewrite array_pred_len_0; auto.
Qed.

Lemma body_makeSet: semax_body Vprog Gprog f_makeSet makeSet_spec.
Proof.
  start_function. forward_call (sh, Z.mul V 8).
  - split. 1: omega. assert (Z.mul 8 (Int.max_signed /8) <= Int.max_signed) by (apply Z_mult_div_ge; intuition).
    apply Z.le_trans with Int.max_signed. 1: omega. rewrite Z.lt_eq_cases; left; apply Int.max_signed_unsigned.
  - Intro rt.
    forward_for_simple_bound V 
      (EX i: Z,
       PROP (forall m : Z, 0 <= m < i -> vvalid (makeSet_discrete_Graph (Z.to_nat i)) m)
       LOCAL (temp _subsets (pointer_val_val rt))
       SEP (whole_graph sh (makeSet_discrete_Graph (Z.to_nat i)) rt; memory_block sh ((V - i) * 8) (pointer_val_val rt))).
    + destruct H. apply Z.le_trans with (Int.max_signed / 8); auto. rewrite Z.lt_eq_cases. left. apply Z_div_lt; intuition.
    + simpl Z.to_nat. Intros. rewrite (whole_graph_empty _ _ (V * 8)); auto. 2: omega. assert (V - 0 = V) by omega. rewrite H1. clear H1. entailer.
    + Intros. eapply semax_seq'. admit.
    + assert (((V - V) * 8)%Z = 0) by omega. rewrite H0; clear H0. rewrite memory_block_zero. forward. apply (exp_right (makeSet_discrete_Graph (Z.to_nat V))).
      entailer. apply (exp_right rt). entailer.
      
Abort.
