Require Import Coq.Classes.Morphisms.
Require Import Coq.omega.Omega.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.EnumEnsembles.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.GraphAsList.
Require Import RamifyCoq.graph.MathGraph.
Require Import RamifyCoq.graph.FiniteGraph.

Section UNION_FIND.

  Context {Vertex: Type}.

  Definition uf_set := Ensemble Vertex.

  Context {Edge: Type}.
  Context {EV: EqDec Vertex eq}.
  Context {EE: EqDec Edge eq}.

  Definition replaceSelfPointingGraph (g: PreGraph Vertex Edge) (null_node: Vertex) : PreGraph Vertex Edge :=
    Build_PreGraph EV EE (vvalid g) (evalid g) (src g) (fun e => if equiv_dec (dst g e) (src g e) then null_node else dst g e).

  Definition uf_graph (pg: PreGraph Vertex Edge) : Prop := forall x n, vvalid pg x -> ~ vvalid pg n -> is_list (replaceSelfPointingGraph pg n) x.

  Definition uf_root (pg: PreGraph Vertex Edge) (x root: Vertex) : Prop := reachable pg x root /\ (forall y, reachable pg root y -> root = y).

  Definition uf_set_in (g: PreGraph Vertex Edge) (s: uf_set) : Prop := (Same_set s (Empty_set Vertex)) \/ (exists rt, s rt /\ forall x, s x <-> uf_root g x rt).

  Definition uf_equiv (g1 g2: PreGraph Vertex Edge) : Prop :=
    (forall x, vvalid g1 x <-> vvalid g2 x) /\ (forall x r1 r2, vvalid g1 x -> uf_root g1 x r1 -> uf_root g2 x r2 -> r1 = r2).

  Definition uf_union (g1: PreGraph Vertex Edge) (e1 e2: Vertex) (g2: PreGraph Vertex Edge) : Prop :=
    forall (S1 S2: uf_set), S1 e1 -> S2 e2 -> uf_set_in g1 S1 -> uf_set_in g1 S2 ->
                            uf_set_in g2 (Union Vertex S1 S2) /\ (forall S, ~ Same_set S S1 -> ~ Same_set S S2 -> uf_set_in g1 S -> uf_set_in g2 S) /\
                            (forall S, uf_set_in g2 S -> Same_set S (Union Vertex S1 S2) \/ uf_set_in g1 S).

End UNION_FIND.

Section LstGraph.

  Context {Vertex: Type}.
  Context {Edge: Type}.
  Context {EV: EqDec Vertex eq}.
  Context {EE: EqDec Edge eq}.

  Class LstGraph (pg: PreGraph Vertex Edge) (out_edge: Vertex -> Edge): Prop :=
    {
      only_one_edge: forall x e, vvalid pg x -> (src pg e = x /\ evalid pg e <-> e = out_edge x)
    }.

  Variable (g: PreGraph Vertex Edge).
  Context {out_edge: Vertex -> Edge}.
  Context {gLst: LstGraph g out_edge}.

  Context {is_null: DecidablePred Vertex}.
  Context {MA: MathGraph g is_null}.

  Fixpoint findRoot (limit: nat) (v: Vertex) : Vertex :=
    let next := (dst g (out_edge v)) in
    if (projT2 is_null) next
    then v
    else if (equiv_dec v next)
         then v
         else match limit with
              | O => v
              | S n => findRoot n next
              end.
  
  Fixpoint findList (bound: nat) (v: Vertex) (l: list Edge) : list Edge :=
    let next := (dst g (out_edge v)) in
    if (projT2 is_null) next
    then rev l
    else if (equiv_dec v next)
         then rev l
         else match bound with
              | O => rev l
              | S n => findList n next (out_edge v :: l)
              end.

  Definition edge_list_head (l : list Edge) (v: Vertex) : Prop :=
    match l with
    | nil => True
    | x :: _ => dst g x = v
    end.

  Lemma findList_foreside: forall b v l, exists l', findList b v l = rev l ++ l'.
  Proof.
    induction b; intros; simpl.
    - exists nil. rewrite app_nil_r. destruct (projT2 is_null (dst g (out_edge v))); [|destruct (equiv_dec v (dst g (out_edge v)))]; auto.
    - destruct (projT2 is_null (dst g (out_edge v))); [|destruct (equiv_dec v (dst g (out_edge v)))]; [exists nil; rewrite app_nil_r; auto .. | ].
      specialize (IHb (dst g (out_edge v)) (out_edge v :: l)). destruct IHb as [l1 ?]. simpl in H. rewrite <- app_assoc in H. exists ((out_edge v :: nil) ++ l1). apply H.
  Qed.

  Lemma valid_path'_findList: forall bound v l, vvalid g v -> edge_list_head l v -> valid_path' g (rev l) -> valid_path' g (findList bound v l).
  Proof.
    induction bound; intros.
    - assert (findList 0 v l = rev l) by (simpl; destruct (projT2 is_null (dst g (out_edge v))); auto; destruct (equiv_dec v (dst g (out_edge v))); auto). rewrite H2. auto.
    - simpl. destruct (projT2 is_null (dst g (out_edge v))); auto. destruct (equiv_dec v (dst g (out_edge v))); auto.
      assert (vvalid g (dst g (out_edge v)) /\ src g (out_edge v) = v /\ evalid g (out_edge v)). {
        destruct is_null as [is_nullP ?]. simpl in *. pose proof (only_one_edge v (out_edge v) H). assert (out_edge v = out_edge v) by auto. rewrite <- H2 in H3. clear H2.
        split; auto. destruct H3. destruct MA. apply valid_graph in H3. simpl in *. destruct H3. destruct H4; auto. exfalso; auto.
      } destruct H2 as [? [? ?]]. apply IHbound; simpl; auto. destruct l; simpl in *.
      + unfold strong_evalid. rewrite H3. split; [|split]; auto.
      + remember (rev l) as l'. clear Heql' l. induction l'.
        * simpl in *. split; auto. rewrite H0, H3. split; auto. unfold strong_evalid. rewrite H3. split; auto.
        * simpl in *. destruct ((l' +:: e) +:: out_edge v) eqn:? . 1: destruct l'; inversion Heql.
          destruct (l' +:: e) eqn:? . 1: destruct l'; inversion Heql0. inversion Heql. subst e1. destruct H1 as [? [? ?]]. split; [|split]; auto. rewrite H7. apply IHl'. auto.
  Qed.

  Lemma findList_preserve_NSP: forall b v l, vvalid g v -> (forall e, In e l -> src g e <> dst g e) -> forall e, In e (findList b v l) -> src g e <> dst g e.
  Proof.
    induction b; intros.
    - assert (findList 0 v l = rev l) by (simpl; destruct (projT2 is_null (dst g (out_edge v))); auto; destruct (equiv_dec v (dst g (out_edge v))); auto).
      rewrite H2 in H1. rewrite <- in_rev in H1. apply H0; auto.
    - simpl in H1. destruct (projT2 is_null (dst g (out_edge v))); [|destruct (equiv_dec v (dst g (out_edge v)))]; [rewrite <- in_rev in H1; apply H0; auto .. |].
      specialize (IHb (dst g (out_edge v)) (out_edge v :: l)). destruct is_null as [is_nullP ?]. destruct MA. simpl in *. destruct gLst. rename only_one_edge0 into H2.
      specialize (H2 v (out_edge v) H). assert (out_edge v = out_edge v) by auto. rewrite <- H2 in H3. clear H2. destruct H3. apply IHb; auto.
      + apply valid_graph in H3. destruct H3. destruct H4; [exfalso |]; auto.
      + intros. destruct H4. 2: apply H0; auto. subst e0. rewrite H2. auto.
  Qed.

  Lemma valid_path_replaceSPG: forall n p, valid_path g p -> (forall e, In e (snd p) -> src g e <> dst g e) -> valid_path (replaceSelfPointingGraph g n) p.
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

  Lemma lstGraph_is_list: forall root null, EnumCovered Vertex (reachable g root) -> vvalid g root -> is_null null -> is_list (replaceSelfPointingGraph g null) root.
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
  Abort.

  Instance MA_vva: ValidVertexAccessible g.
  Proof.
    apply (Build_ValidVertexAccessible _ (fun l => filter (fun e => if (projT2 is_null) (dst g e) then false else true) l)).
    intros. destruct is_null as [is_nullP ?]. simpl. destruct MA. simpl in *.
    rewrite filter_In. intuition.
    - destruct (s (dst g e)). inversion H2. specialize (valid_not_null (dst g e)). rewrite Forall_forall in H. specialize (H _ H1). apply valid_graph in H.
      destruct H. destruct H0; intuition.
    - destruct (s (dst g e)); auto. specialize (valid_not_null (dst g e)). exfalso; apply valid_not_null; auto.
  Qed.

End LstGraph.

Global Existing Instance MA_vva.
