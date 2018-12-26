Require Import Coq.Classes.Morphisms.
Require Import Coq.omega.Omega.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.EnumEnsembles.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.graph_gen.
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
      no_loop_path: forall x p, pg |= p is x ~o~> x satisfying (fun _ => True) -> p = (x, nil)
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

  Lemma lst_reachable_unique: forall v1 p1 v2 p2 x r1 r2 P,
      g |= (v1, p1) is x ~o~> r1 satisfying P -> g |= (v2, p2) is x ~o~> r2 satisfying P -> length p1 <= length p2 ->
      exists p3, p2 = p1 ++ p3 /\ g |= (r1, p3) is r1 ~o~> r2 satisfying P.
  Proof.
    intros. destruct H as [[? ?] ?]. destruct H0 as [[? ?] ?]. simpl in H, H0. subst v1 v2.
    pose proof H3. pose proof H5. destruct H as [? _]. destruct H0 as [? _]. destruct (lst_valid_path_unique _ _ _ H H0 H1) as [p3 ?]. clear H H0.
    exists p3. split; auto. split; [split |].
    - simpl. auto.
    - destruct p3.
      + rewrite app_nil_r in H6. subst p2. simpl. rewrite H2 in H4. auto.
      + rewrite H6 in H4. rewrite pfoot_app_cons with (v2 := r1) in H4. auto.
    - subst p2. apply good_path_app in H5. destruct H5 as [_ ?]. rewrite H2 in H. auto.
  Qed.
  
  Lemma lst_reachable_unique':
    forall p1 p2 x r1 r2 P, g |= p1 is x ~o~> r1 satisfying P -> g |= p2 is x ~o~> r2 satisfying P -> length (snd p1) <= length (snd p2) -> g |= r1 ~o~> r2 satisfying P.
  Proof.
    intros. destruct p1 as [v1 p1]. destruct p2 as [v2 p2]. simpl in H1. destruct (lst_reachable_unique v1 p1 v2 p2 x r1 r2 P H H0 H1) as [p3 [? ?]]. exists (r1, p3); auto.
  Qed.

  Lemma lst_src_dst_determine_path: forall p x y P, g |= p is x ~o~> y satisfying P -> unique (fun pa : path => g |= pa is x ~o~> y satisfying P) p.
  Proof.
    intros. hnf. split; auto. intros p2 ?. destruct p as [v1 p1]. destruct p2 as [v2 p2]. f_equal.
    - destruct H as [[? _] _]. destruct H0 as [[? _] _]. simpl in H, H0. subst v1 v2; auto.
    - destruct (le_dec (length p1) (length p2)).
      + destruct (lst_reachable_unique v1 p1 v2 p2 x y y P H H0 l) as [p3 [? ?]].
        assert (g |= (y, p3) is y ~o~> y satisfying (fun _ => True)) by (apply reachable_by_path_weaken with P; auto; unfold Included, Ensembles.In; intros; auto).
        apply no_loop_path in H3. inversion H3. subst p3 p2. rewrite app_nil_r; auto.
      + assert (length p2 <= length p1) by intuition. rename H1 into l. destruct (lst_reachable_unique v2 p2 v1 p1 x y y P H0 H l) as [p3 [? ?]].
        assert (g |= (y, p3) is y ~o~> y satisfying (fun _ => True)) by (apply reachable_by_path_weaken with P; auto; unfold Included, Ensembles.In; intros; auto).
        apply no_loop_path in H3. inversion H3. subst p3 p1. rewrite app_nil_r; auto.
  Qed.

  Lemma lst_path_NoDup: forall p x y P, g |= p is x ~o~> y satisfying P -> NoDup (snd p).
  Proof.
    intros. destruct p as [v p]. simpl. destruct (ListDec.NoDup_dec EE p); auto. exfalso. destruct (Dup_cyclic _ n) as [e [p1 [p2 [p3 ?]]]]. subst p. clear n. simpl in H.
    pose proof H. apply reachable_by_path_app_cons in H0. destruct H0 as [? _]. replace (p1 ++ e :: p2 ++ e :: p3) with ((p1 ++ e :: p2) ++ e :: p3) in H.
    - apply reachable_by_path_app_cons in H. destruct H as [? _]. apply lst_src_dst_determine_path in H0. destruct H0. apply H1 in H. inversion H.
      rewrite <- (app_nil_r p1) in H3 at 1. apply app_inv_head in H3. inversion H3.
    - rewrite <- app_assoc. simpl. auto.
  Qed.

  Lemma lst_reachable_or: forall x r1 r2, reachable g x r1 -> reachable g x r2 -> reachable g r1 r2 \/ reachable g r2 r1.
  Proof.
    intros. destruct H as [p1 ?]. destruct H0 as [p2 ?]. destruct (le_dec (length (snd p1)) (length (snd p2))); [left | right].
    - apply (lst_reachable_unique' p1 p2 x); auto.
    - apply (lst_reachable_unique' p2 p1 x); intuition.
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

  Lemma dst_step: forall x pa, vvalid g x -> dst g (out_edge x) =  pa -> forall y, step g x y <-> y = pa.
  Proof.
    intros. subst pa. rewrite step_spec; split; intros.
    - destruct H0 as [e [? [? ?]]]. pose proof (only_one_edge x e H). simpl in H3. pose proof (proj1 H3 (conj H1 H0)). subst e. auto.
    - exists (out_edge x). subst y. pose proof (only_one_edge x (out_edge x) H). simpl in H0. assert ((out_edge x) = (out_edge x)) by auto. rewrite <- H0 in H1. intuition.
  Qed.

  Lemma vvalid_src_evalid: forall x, vvalid g x -> src g (out_edge x) = x /\ evalid g (out_edge x).
  Proof. intros. assert ((out_edge x) = (out_edge x)) by auto. pose proof (only_one_edge x (out_edge x) H). rewrite <- H1 in H0. auto. Qed.

  Lemma dst_not_reachable: forall x pa y, vvalid g x -> dst g (out_edge x) = pa -> reachable g pa y -> ~ reachable g y x.
  Proof.
    intros. intro. assert (g |= (x, (out_edge x) :: nil) is x ~o~> pa satisfying (fun _ => True)). {
      split; split; auto.
      - simpl. unfold strong_evalid. rewrite H0. pose proof (vvalid_src_evalid x H). destruct H3. rewrite H3.
        split; [|split; [|split]]; auto. apply reachable_head_valid in H1. auto.
      - red. rewrite Forall_forall. split; intros; auto.
    } assert (reachable g pa x) by (apply reachable_trans with y; auto). destruct H4 as [ppa ?].
    pose proof (reachable_by_path_merge _ _ _ _ _ _ _ H3 H4). apply no_loop_path in H5. unfold path_glue in H5. simpl in H5. inversion H5.
  Qed.

  Lemma gen_dst_preserve_lst: forall x pa, ~ reachable g pa x -> vvalid g x -> LstGraph (pregraph_gen_dst g (out_edge x) pa) out_edge.
  Proof.
    intros. constructor. 1: simpl; apply only_one_edge. intro y; intros. destruct (in_dec EE (out_edge x) (snd p)).
    - destruct p as [p l]. simpl in i. apply (in_split_not_in_first EE) in i. destruct i as [l1 [l2 [? ?]]]. rewrite H2 in H1. apply reachable_by_path_app_cons in H1.
      destruct H1. simpl src in H1. simpl dst in H4. unfold updateEdgeFunc in H4. destruct (equiv_dec (out_edge x) (out_edge x)).
      2: compute in c; exfalso; apply c; auto. clear e. rewrite no_edge_gen_dst_equiv in H1. 2: simpl; auto.
      pose proof (vvalid_src_evalid x H0). destruct H5. rewrite H5 in H1. destruct (in_dec EE (out_edge x) l2).
      + apply (in_split_not_in_last EE) in i. destruct i as [l3 [l4 [? ?]]]. rewrite H7 in H4. apply reachable_by_path_app_cons in H4. destruct H4 as [_ ?].
        simpl in H4. unfold updateEdgeFunc in H4. destruct (equiv_dec (out_edge x) (out_edge x)). 2: compute in c; exfalso; apply c; auto. clear e.
        rewrite no_edge_gen_dst_equiv in H4. 2: simpl; auto. pose proof (reachable_by_path_merge _ _ _ _ _ _ _ H4 H1). apply reachable_by_path_is_reachable in H9. exfalso; auto.
      + rewrite no_edge_gen_dst_equiv in H4. 2: simpl; auto. pose proof (reachable_by_path_merge _ _ _ _ _ _ _ H4 H1). apply reachable_by_path_is_reachable in H7. exfalso; auto.
    - rewrite no_edge_gen_dst_equiv in H1; auto. apply no_loop_path in H1. auto.
  Qed.

End LstGraph.
