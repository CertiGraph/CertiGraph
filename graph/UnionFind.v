Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.lib.Ensembles_ext.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.graph_gen.
Require Import RamifyCoq.graph.GraphAsList.
Require Import RamifyCoq.graph.MathGraph.
Require Import RamifyCoq.graph.LstGraph.

Section UNION_FIND.

  Context {Vertex: Type}.

  Definition uf_set := Ensemble Vertex.

  Context {Edge: Type}.
  Context {EV: EqDec Vertex eq}.
  Context {EE: EqDec Edge eq}.

  Definition replaceSelfPointingGraph (g: PreGraph Vertex Edge) (null_node: Vertex) : PreGraph Vertex Edge :=
    Build_PreGraph EV EE (vvalid g) (evalid g) (src g) (fun e => if equiv_dec (dst g e) (src g e) then null_node else dst g e).

  Definition uf_graph (pg: PreGraph Vertex Edge) : Prop := forall x, vvalid pg x -> is_list pg x.

  Definition uf_root (pg: PreGraph Vertex Edge) (x root: Vertex) : Prop := reachable pg x root /\ (forall y, reachable pg root y -> root = y).

  Definition uf_set_in (g: PreGraph Vertex Edge) (s: uf_set) : Prop := (Same_set s (Empty_set Vertex)) \/ (exists rt, s rt /\ forall x, s x <-> uf_root g x rt).

  Definition uf_equiv (g1 g2: PreGraph Vertex Edge) : Prop :=
    (forall x, vvalid g1 x <-> vvalid g2 x) /\ (forall x r1 r2, vvalid g1 x -> uf_root g1 x r1 -> uf_root g2 x r2 -> r1 = r2).

  Definition uf_union (g1: PreGraph Vertex Edge) (e1 e2: Vertex) (g2: PreGraph Vertex Edge) : Prop :=
    forall (S1 S2: uf_set), S1 e1 -> S2 e2 -> uf_set_in g1 S1 -> uf_set_in g1 S2 ->
                            uf_set_in g2 (Union Vertex S1 S2) /\ (forall S, ~ Same_set S S1 -> ~ Same_set S S2 -> uf_set_in g1 S -> uf_set_in g2 S) /\
                            (forall S, uf_set_in g2 S -> Same_set S (Union Vertex S1 S2) \/ uf_set_in g1 S).
  
  Variable (g: PreGraph Vertex Edge).
  Context {out_edge: Vertex -> Edge}.
  Context (gLst: LstGraph g out_edge).

  Lemma uf_root_unique: forall x r1 r2, uf_root g x r1 -> uf_root g x r2 -> r1 = r2.
  Proof. intros. destruct H, H0. pose proof (lst_reachable_or _ _ _ _ _ H H0). destruct H3; [apply H1 | symmetry; apply H2]; auto. Qed.

  Lemma uf_root_reachable: forall x pa root, reachable g x pa -> uf_root g pa root -> uf_root g x root.
  Proof. intros. destruct H0. split; intros; [apply reachable_trans with pa | apply H1]; auto. Qed.

  Lemma uf_root_edge: forall x pa root, vvalid g x -> dst g (out_edge x) = pa -> uf_root g pa root -> uf_root g x root.
  Proof.
    intros. apply (uf_root_reachable x pa); auto. apply reachable_edge with x.
    - apply reachable_refl; auto.
    - hnf. split; [|split]; auto.
      + destruct H1. apply reachable_head_valid in H1. auto.
      + rewrite step_spec. exists (out_edge x). pose proof (vvalid_src_evalid _ _ _ H). destruct H2. split; auto.
  Qed.

  Lemma uf_root_gen_dst: forall x y pa, uf_root g x pa -> ~ reachable g pa x -> reachable g y x -> uf_root (pregraph_gen_dst g (out_edge x) pa) y pa.
  Proof.
    intros ? ? ? Hv Hn. assert (vvalid g x) by (destruct Hv; apply reachable_head_valid in H; auto). split; intros.
    - destruct H0 as [[p l] ?]. exists (p, l +:: (out_edge x)).
      assert ((p, l +:: out_edge x) = path_glue (p, l) (x, (out_edge x) :: nil)) by (unfold path_glue; simpl; auto). rewrite H1. clear H1. apply reachable_by_path_merge with x. 
      + rewrite no_edge_gen_dst_equiv; auto. intro. simpl in H1. apply in_split in H1. destruct H1 as [l1 [l2 ?]]. subst l.
        assert (paths_meet_at g (p, l1) (x, out_edge x :: l2) x). {
          hnf; split. 2: simpl; auto. destruct H0 as [_ [? _]]. apply pfoot_split in H0. pose proof (vvalid_src_evalid _ _ _ H). destruct H1. rewrite H1 in H0. auto.
        } assert ((p, l1 ++ out_edge x :: l2) = path_glue (p, l1) (x, (out_edge x) :: l2)) by (unfold path_glue; simpl; auto). rewrite H2 in H0; clear H2.
        apply reachable_by_path_split_glue with (n := x) in H0; auto. clear H1. destruct H0. apply no_loop_path in H1. inversion H1.
      + assert (valid_path (pregraph_gen_dst g (out_edge x) pa) (x, out_edge x :: nil)). {
          simpl. unfold strong_evalid. simpl. unfold updateEdgeFunc. destruct (equiv_dec (out_edge x) (out_edge x)). 2: compute in c; exfalso; apply c; auto.
          pose proof (vvalid_src_evalid _ _ _ H). destruct H1. rewrite H1. split; [|split; [|split]]; auto. destruct Hv. apply reachable_foot_valid in H3; auto.
        } split; split; auto.
        * simpl. unfold updateEdgeFunc. destruct (equiv_dec (out_edge x) (out_edge x)); auto. compute in c; exfalso; apply c; auto.
        * rewrite path_prop_equiv; auto.
    - destruct Hv. apply H3. rewrite not_reachable_gen_dst_equiv in H1; auto. pose proof (vvalid_src_evalid _ _ _ H). destruct H4. rewrite H4; auto.
  Qed.
    
  Lemma uf_equiv_refl: uf_equiv g g.
  Proof. hnf; split; intros; intuition. destruct H0, H1. destruct (@lst_reachable_or _ _ _ _ _ _ gLst _ _ _ H0 H1); [apply H2 | symmetry; apply H3]; auto. Qed.

  Lemma valid_path_replaceSPG: forall n p, valid_path g p -> (forall e, List.In e (snd p) -> src g e <> dst g e) -> valid_path (replaceSelfPointingGraph g n) p.
  Proof.
    intros. destruct p as [v p]. revert v H H0. induction p; intros.
    - simpl in *; auto.
    - simpl in H |-* . destruct H. split; auto. simpl in H0. assert (strong_evalid g a) by (destruct p; [|destruct H1]; auto). destruct H2 as [? [? ?]].
      assert (src g a <> dst g a) by (apply H0; left; auto).
      assert (strong_evalid (replaceSelfPointingGraph g n) a) by (hnf; simpl; split; [|split]; auto; destruct (equiv_dec (dst g a) (src g a)); [exfalso|]; auto).
      destruct p eqn:? ; auto. destruct H1 as [? [? ?]]. split; auto. split.
      + destruct (equiv_dec (dst g a) (src g a)); [exfalso|]; auto.
      + unfold valid_path in IHp at 2. unfold replaceSelfPointingGraph in IHp at 1. simpl src in IHp.
        cut (src g e = src g e /\ valid_path' (replaceSelfPointingGraph g n) (e :: l)). 1: intros HS; destruct HS; auto. apply IHp. 1: unfold valid_path; split; auto.
        simpl. intros. apply H0. right. simpl. auto.
  Qed.

  (*Lemma lstGraph_is_list: forall root null, EnumCovered Vertex (reachable g root) -> vvalid g root -> is_null null -> is_list (replaceSelfPointingGraph g null) root.
  Proof.
    intros. hnf. exists (root, (findList (length (proj1_sig X)) root nil)). split.
    - apply valid_path_replaceSPG.
      + unfold valid_path. destruct (findList (length (proj1_sig X)) root nil) eqn:? ; auto. split.
        * remember (length (proj1_sig X)) as n. destruct n; simpl in Heql.
          -- destruct (projT2 is_null (dst g (out_edge root))). 1: inversion Heql. destruct (equiv_dec root (dst g (out_edge root))); inversion Heql.
          -- destruct (projT2 is_null (dst g (out_edge root))). 1: inversion Heql. destruct (equiv_dec root (dst g (out_edge root))). 1: inversion Heql.
             destruct (findList_foreside n (dst g (out_edge root)) (out_edge root :: nil)) as [l' ?]. rewrite H1 in Heql. simpl in Heql. inversion Heql.
             destruct gLst. rename only_one_edge0 into H2. specialize (H2 root (out_edge root) H). assert (out_edge root = out_edge root) by auto.
             rewrite <- H2 in H5. destruct H5; auto.
        * rewrite <- Heql. apply valid_path'_findList; simpl; auto.
      + simpl. apply findList_preserve_NSP; auto.
    - intros. pose proof H1. destruct H2 as [py ?]. exists py. split.
      + hnf. split; auto. intros py' ?. destruct py as [h1 ?]. destruct py' as [h2 l']. assert (h1 = root) by (destruct H2 as [[? _] _]; simpl in H2; auto).
        assert (h2 = root) by (destruct H3 as [[? _] _]; simpl in H3; auto). subst h1 h2. f_equal. revert l' l H3 H2. induction l'; intros.
        * destruct l; auto.
  Abort.*)

  Context {DV DE DG: Type}.
  Context {P: LabeledGraph Vertex Edge DV DE DG -> Type}.

  Notation Graph := (GeneralGraph Vertex Edge DV DE DG P).
  Local Coercion pg_lg : LabeledGraph >-> PreGraph.
  Local Coercion lg_gg : GeneralGraph >-> LabeledGraph.

  Definition rank_unchanged (g1 g2: Graph) : Prop := forall v, vvalid g1 v -> vvalid g2 v -> vlabel g1 v = vlabel g2 v.

  Definition findS (g1: Graph) (x: Vertex) (g2: Graph) := 
    (predicate_partialgraph g1 (fun n => ~ reachable g1 x n)) ~=~ (predicate_partialgraph g2 (fun n => ~ reachable g1 x n)) /\ uf_equiv g1 g2 /\ rank_unchanged g1 g2.
  
End UNION_FIND.
