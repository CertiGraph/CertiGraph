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

Section LstGraph.

  Context {Vertex: Type}.
  Context {Edge: Type}.
  Context {EV: EqDec Vertex eq}.
  Context {EE: EqDec Edge eq}.

  Class LstGraph (pg: PreGraph Vertex Edge) (out_edge: Vertex -> Edge): Prop :=
    {
      only_one_edge: forall x e, vvalid pg x -> (src pg e = x /\ evalid pg e <-> e = out_edge x);
      all_valid: forall x, vvalid pg x -> vvalid pg (dst pg (out_edge x))
    }.

  Variable (g: PreGraph Vertex Edge).
  Context {out_edge: Vertex -> Edge}.
  Context (gLst: LstGraph g out_edge).

  Lemma lst_valid_path_unique: forall v p1 p2, valid_path g (v, p1) -> valid_path g (v, p2) -> length p1 <= length p2 -> exists p3, p2 = p1 ++ p3.
  Proof.
    intros. revert p1 H H1.
    apply (rev_ind (fun p1 => (valid_path g (v, p1) -> length p1 <= length p2 -> exists p3 : list Edge, p2 = p1 ++ p3))); intros.
    - exists p2. simpl. auto.
    - pose proof H1. apply valid_path_app in H3. destruct H3 as [? _]. apply H in H3.
      + destruct H3 as [p4 ?]. destruct p4.
        * rewrite app_nil_r in H3. subst p2. rewrite app_length in H2. simpl in H2. exfalso; intuition.
        * exists p4. subst p2. rewrite <- app_assoc. simpl. f_equal. f_equal. clear H H2. pose proof H1. pose proof H0. apply pfoot_split in H. apply pfoot_split in H2.
          assert (strong_evalid g x) by (apply (valid_path_strong_evalid _ _ _ _ H1); rewrite in_app_iff; right; intuition). destruct H3 as [? _].
          assert (strong_evalid g e) by (apply (valid_path_strong_evalid _ _ _ _ H0); rewrite in_app_iff; right; intuition). destruct H4 as [? [? _]]. rewrite <- H2 in H5.
          assert (x = out_edge (pfoot g (v, l))) by (apply only_one_edge; auto). assert (e = out_edge (pfoot g (v, l))) by (apply only_one_edge; auto).
          rewrite <- H6 in H7. auto.
      + rewrite app_length in H2. simpl in H2. intuition.
  Qed.
  
  Lemma lst_reachable_unique:
    forall p1 p2 x r1 r2 P, g |= p1 is x ~o~> r1 satisfying P -> g |= p2 is x ~o~> r2 satisfying P -> length (snd p1) <= length (snd p2) -> g |= r1 ~o~> r2 satisfying P.
  Proof.
    intros. destruct H as [[? ?] ?]. destruct H0 as [[? ?] ?]. destruct p1 as [v1 p1]. destruct p2 as [v2 p2]. simpl in H, H0, H1. subst v1 v2.
    pose proof H3. pose proof H5. destruct H as [? _]. destruct H0 as [? _]. destruct (lst_valid_path_unique _ _ _ H H0 H1) as [p3 ?]. clear H H0.
    exists (r1, p3). split; [split |].
    - simpl. auto.
    - destruct p3.
      + rewrite app_nil_r in H6. subst p2. simpl. rewrite H2 in H4. auto.
      + rewrite H6 in H4. rewrite pfoot_app_cons with (v2 := r1) in H4. auto.
    - subst p2. apply good_path_app in H5. destruct H5 as [_ ?]. rewrite H2 in H. auto.
  Qed.

  Lemma lst_reachable_or: forall x r1 r2, reachable g x r1 -> reachable g x r2 -> reachable g r1 r2 \/ reachable g r2 r1.
  Proof.
    intros. destruct H as [p1 ?]. destruct H0 as [p2 ?]. destruct (le_dec (length (snd p1)) (length (snd p2))); [left | right].
    - apply (lst_reachable_unique p1 p2 x); auto.
    - apply (lst_reachable_unique p2 p1 x); intuition.
  Qed.

  Lemma lst_self_loop: forall x y, dst g (out_edge x) = x -> reachable g x y -> x = y.
  Proof.
    intros. destruct H0 as [[v p] ?]. assert (v = x) by (destruct H0 as [[? _] _]; simpl in H0; auto). subst v. induction p.
    - destruct H0 as [[_ ?] _]. simpl in H0. auto.
    - assert (g |= (dst g a, p) is (dst g a) ~o~> y satisfying (fun _ => True)). {
        clear IHp. destruct H0 as [[? ?] [? ?]]. pose proof H2. apply valid_path_cons in H4. split; split; auto.
        - rewrite pfoot_cons in H1. auto.
        - rewrite path_prop_equiv; intros; auto. }
      assert (dst g a = x). {
        destruct H0 as [_ [? _]]. simpl in H0. destruct H0. assert (strong_evalid g a) by (destruct p; intuition). clear H2. destruct H3 as [? [? ?]]. rewrite <- H0 in H3.
        assert (a = out_edge x) by (apply only_one_edge; auto). rewrite <- H5 in H. auto.
      } apply IHp. rewrite H2 in H1. auto.
  Qed.

  Lemma lst_out_edge_only_one: forall x z y, dst g (out_edge x) = z -> reachable g x y -> ~ reachable g z y -> x = y.
  Proof.
    intros. apply reachable_ind.reachable_ind in H0. destruct H0; auto. destruct H0 as [z' [? [? ?]]]. hnf in H0. destruct H0 as [? [? ?]].
    rewrite step_spec in H5. destruct H5 as [e [? [? ?]]]. assert (e = out_edge x) by (apply only_one_edge; auto). rewrite <- H8 in H. rewrite H in H7.
    subst z'. exfalso; auto.
  Qed.

  Context {is_null: DecidablePred Vertex}.
  Context {MA: MathGraph g is_null}.
  
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
      intros. destruct H4. 2: apply H0; auto. subst e0. rewrite H2. auto.
  Qed.

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
