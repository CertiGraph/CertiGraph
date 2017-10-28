Require Import Coq.Sets.Ensembles.
Require Import Coq.Lists.List.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.Ensembles_ext.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.reachable_computable.
Require Import RamifyCoq.graph.graph_gen.
Require Import RamifyCoq.graph.FiniteGraph.
Require Import RamifyCoq.graph.MathGraph.
Require Import RamifyCoq.graph.LstGraph.
Require Import RamifyCoq.graph.UnionFind.

Section UnionFindGraph.

  Context {V E: Type}.
  Context {VE: EqDec V eq}.
  Context {EE: EqDec E eq}.

  Context {isNullDec: DecidablePred V}.
  Context {out_edge: V -> E}.

  (* Context {ufg: UnionFindGraph}. *)
  
  Class LiMaFin (g: PreGraph V E) :=
    {
      li: LstGraph g out_edge;
      ma: MathGraph g isNullDec;
      fin: FiniteGraph g
    }.

  Context {DV DE DG: Type}.

  Definition LGraph := LabeledGraph V E DV DE DG.
  Definition Graph := (GeneralGraph V E DV DE DG (fun g => LiMaFin (pg_lg g))).

  Definition Graph_LGraph (G: Graph): LGraph := lg_gg G.

  Local Coercion Graph_LGraph: Graph >-> LGraph.
  Local Identity Coercion LGraph_LabeledGraph: LGraph >-> LabeledGraph.
  Local Coercion pg_lg: LabeledGraph >-> PreGraph.

  Instance maGraph(G: Graph): MathGraph G isNullDec := @ma G (@sound_gg _ _ _ _ _ _ _ _ G).
  Instance finGraph (G: Graph): FiniteGraph G := @fin G (@sound_gg _ _ _ _ _ _ _ _ G).
  Instance liGraph (G: Graph):  LstGraph G out_edge := @li G (@sound_gg _ _ _ _ _ _ _ _ G).

  Definition vgamma (g: LGraph) (x: V) : DV * V := (vlabel g x, let target := dst (pg_lg g) (out_edge x) in if (projT2 isNullDec target) then x else target).

  Lemma valid_parent: forall (g: Graph) v n p, vvalid g v -> vgamma g v = (n, p) -> vvalid g p.
  Proof.
    intros. unfold vgamma in H0. simpl in H0. inversion H0. clear H0 H2. destruct (projT2 isNullDec (dst g (out_edge v))); auto.
    assert (~ isNullDec (dst g (out_edge v))) by (intro; apply n0; auto).
    pose proof (only_one_edge v (out_edge v) H). assert (out_edge v = out_edge v) by auto. rewrite <- H1 in H2. destruct H2.
    pose proof (valid_graph _ _ H4). destruct H5 as [_ [? | ?]]; auto. exfalso; auto.
  Qed.

  Lemma parent_loop: forall (g: Graph) v n y, vgamma g v = (n, v) -> reachable g v y -> v = y.
  Proof.
    intros. unfold vgamma in H. destruct (projT2 isNullDec (dst g (out_edge v))).
    - apply (lst_out_edge_only_one g _ v (dst g (out_edge v)) y); auto. intro. apply reachable_head_valid in H1. apply (valid_not_null g (dst g (out_edge v)) H1); auto.
    - apply (lst_self_loop _ (liGraph g)) in H0; auto. inversion H. rewrite H3. auto.
  Qed.

  Lemma gamma_parent_reachable_included: forall (g: Graph) x r pa, vvalid g x -> vgamma g x = (r, pa) -> Included (reachable g pa) (reachable g x).
  Proof.
    intros. intro y; intros. unfold vgamma in H0. destruct (projT2 isNullDec (dst g (out_edge x))).
    - inversion H0. auto.
    - apply edge_reachable_by with pa; auto. split; auto. split.
      + apply reachable_head_valid in H1; auto.
      + inversion H0. rewrite H4. rewrite (dst_step _ (liGraph g) _ _ H H4). auto.
  Qed.

  Lemma Prop_join_reachable_parent: forall (g: Graph) x r pa,
      vvalid g x -> vgamma g x = (r, pa) ->
      Prop_join
        (reachable g pa)
        (Intersection _ (reachable g x) (Complement V (reachable g pa)))
        (reachable g x).
  Proof.
    intros. apply Ensemble_join_Intersection_Complement.
    - eapply gamma_parent_reachable_included; eauto.
    - intros. apply decidable_prop_decidable. pose proof (finGraph g).
      apply (@reachable_decidable_prime _ _ _ _ _ _ (maGraph g)).
      + apply LocalFiniteGraph_FiniteGraph; auto.
      + apply (valid_parent _ x r); auto.
      + apply FiniteGraph_EnumCovered; auto.
  Qed.

  Definition Graph_gen_redirect_parent (g: Graph) (x: V) (pa: V) (H: weak_valid g pa) (Hv: vvalid g x) (Hn: ~ reachable g pa x): Graph.
  Proof.
    refine (generalgraph_gen_dst g (out_edge x) pa _). constructor.
    - simpl. apply (gen_dst_preserve_lst g (liGraph g)); auto.
    - apply (gen_dst_preserve_math g (out_edge x) pa (maGraph g) H).
    - apply (gen_dst_preserve_finite g (out_edge x) pa (finGraph g)).
  Defined.

  Lemma Graph_reachable_dec: forall (G: Graph) x, Decidable (vvalid G x) -> forall y, Decidable (reachable G x y).
  Proof.
    intros. apply reachable_decidable with (is_null := isNullDec); auto.
    + apply maGraph.
    + apply LocalFiniteGraph_FiniteGraph, finGraph.
    + apply FiniteGraph_EnumCovered, finGraph.
  Qed.

  Definition Graph_vgen (G: Graph) (x: V) (d: DV) : Graph := generalgraph_vgen G x d (sound_gg G).

  Lemma uf_root_vgamma: forall (g: Graph) v n, vvalid g v -> vgamma g v = (n, v) -> uf_root g v v.
  Proof. intros. split; [apply reachable_refl | intros; apply (parent_loop g _ n)]; auto. Qed.

  Lemma vgamma_not_dst: forall (g: Graph) x r pa, vgamma g x = (r, pa) -> pa <> x -> dst g (out_edge x) = pa.
  Proof. intros. unfold vgamma in H. destruct (projT2 isNullDec (dst g (out_edge x))); inversion H; [exfalso |]; auto. Qed.

  Lemma vgamma_not_edge: forall (g: Graph) x r pa, vvalid g x -> vgamma g x = (r, pa) -> pa <> x -> g |= x ~> pa.
  Proof.
    intros. assert (vvalid g pa) by (apply valid_parent in H0; auto). hnf. split; [|split]; auto.
    apply (vgamma_not_dst g x r) in H1; auto. rewrite step_spec. exists (out_edge x).
    pose proof (vvalid_src_evalid _ (liGraph g) _ H). destruct H3. split; auto.
  Qed.

  Lemma vgamma_not_reachable': forall (g: Graph) x r pa y, vvalid g x -> vgamma g x = (r, pa) -> pa <> x -> reachable g pa y -> ~ reachable g y x.
  Proof. intros. apply (dst_not_reachable _ (liGraph g) _ pa); auto. apply (vgamma_not_dst g x r); auto. Qed.

  Lemma vgamma_not_reachable: forall (g: Graph) x r pa, vvalid g x -> vgamma g x = (r, pa) -> pa <> x -> ~ reachable g pa x.
  Proof. intros. assert (vvalid g pa) by (apply valid_parent in H0; auto). apply (vgamma_not_reachable' g x r pa pa); auto. apply reachable_refl; auto. Qed.
  
  Lemma uf_root_not_eq_root_vgamma: forall (g: Graph) x r pa root, vgamma g x = (r, pa) -> uf_root g x root -> x <> root -> x <> pa.
  Proof.
    intros. unfold vgamma in H. destruct (projT2 isNullDec (dst g (out_edge x))). 
    - destruct H0. apply reachable_ind.reachable_ind in H0. destruct H0. 1: exfalso; auto. destruct H0 as [z [[? [? ?]] [? ?]]]. rewrite step_spec in H4.
      destruct H4 as [ed [? [? ?]]]. pose proof (conj H7 H4). rewrite (@only_one_edge _ _ _ _ g _ (liGraph g)) in H9; auto. subst ed. rewrite H8 in p.
      exfalso. apply (@valid_not_null _ _ _ _ g _ (maGraph g)) in H3; auto.
    - inversion H. clear H H3. assert (vvalid g x) by (destruct H0; apply reachable_head_valid in H; auto).
      assert (g |= (x, (out_edge x) :: nil) is x ~o~> pa satisfying (fun _ => True)). {
        split; split; intros; hnf; simpl; auto. unfold strong_evalid. assert (out_edge x = out_edge x) by auto. rewrite <- (@only_one_edge _ _ _ _ g _ (liGraph g)) in H2; auto.
        destruct H2. split; [|split]; auto. rewrite H2. split; auto. apply (@valid_graph _ _ _ _ g _ (maGraph g)) in H3. destruct H3 as [_ [? | ?]]; auto.
        hnf in H3. exfalso; auto.
      } rewrite H4. intro. rewrite <- H3 in H2. apply (@no_loop_path _ _ _ _ g _ (liGraph g)) in H2. inversion H2.
  Qed.

  Lemma vgamma_uf_root: forall (g: Graph) x r pa root, vvalid g x -> vgamma g x = (r, pa) -> uf_root g x root -> x <> root -> uf_root g pa root.
  Proof.
    intros. pose proof (uf_root_not_eq_root_vgamma g _ _ _ _ H0 H1 H2). destruct H1. split; auto. pose proof (valid_parent g _ _ _ H H0).  
    assert (Decidable (reachable g pa root)) by (apply Graph_reachable_dec; left; auto). apply decidable_prop_decidable in H6. destruct H6; auto. exfalso.
    pose proof (lst_out_edge_only_one g (liGraph g) x pa root). simpl in H7. apply H2. apply H7; auto. apply (vgamma_not_dst _ _ r); auto.
  Qed.
  
  Instance fml : FML_General V E DV DE DG LiMaFin out_edge isNullDec. Proof. constructor; intros; destruct X; auto. Defined.

  Global Existing Instance fml.

  Lemma findS_preserves_vgamma: forall (g1 g2: Graph) x r pa, vvalid g1 x -> vgamma g1 x = (r, pa) -> pa <> x -> findS g1 pa g2 -> vgamma g2 x = (r, pa).
  Proof.
    intros. assert (Hr: ~ reachable g1 pa x) by (apply vgamma_not_reachable with r; auto). unfold vgamma in *. destruct (projT2 isNullDec (dst g1 (out_edge x))).
    1: inversion H0; exfalso; auto. rewrite <- H0. destruct H2 as [? [[? ?] ?]]. f_equal.
    - assert (vvalid g2 x) by (rewrite <- H3; auto). specialize (H5 x H H6). unfold Graph_LGraph. rewrite H5. auto.
    - assert (evalid (predicate_partialgraph (lg_gg g1) (fun n : V => ~ reachable (lg_gg g1) pa n)) (out_edge x)). {
        simpl. hnf. pose proof (vvalid_src_evalid _ (liGraph g1) _ H). unfold Graph_LGraph in H6. destruct H6. rewrite H6. split; auto.
      } destruct H2 as [_ [? [_ ?]]]. pose proof H6. rewrite H2 in H8. clear H2. specialize (H7 _ H6 H8). simpl in H7. unfold Graph_LGraph. rewrite <- H7.
      destruct (projT2 isNullDec (dst (lg_gg g1) (out_edge x))); [exfalso |]; auto.
  Qed.

  Lemma the_same_root_union: forall (g g1 g2: Graph) x y root,
      vvalid g x -> vvalid g y -> uf_equiv g g1 -> uf_equiv g1 g2 -> uf_root g1 x root -> uf_root g2 y root -> uf_union g x y g2.
  Proof. intros. apply (same_root_union g g1 g2 x y root); auto. Qed.

  Lemma uf_equiv_root_the_same: forall (g1 g2: Graph) x root, uf_equiv g1 g2 -> uf_root g1 x root <-> uf_root g2 x root.
  Proof. intros. pose proof (@uf_equiv_the_same_root _ _ _ _ _ _ _ _ out_edge isNullDec fml g1 g2 x root H). apply H0. Qed.

  Lemma uf_equiv_not_reachable: forall (g1 g2: Graph) x r pa root,
      vvalid g1 x -> vgamma g1 x = (r, pa) -> pa <> x -> uf_equiv g1 g2 -> uf_root g2 pa root -> ~ reachable g2 root x.
  Proof.
    intros. pose proof H3. rewrite <- (uf_equiv_root_the_same _ _ pa root H2) in H4. destruct H3. intro. apply H5 in H6. subst x.
    pose proof (vgamma_not_reachable g1 root r pa H H0 H1). destruct H4. auto.
  Qed.

  Lemma graph_gen_redirect_parent_equiv': forall (g1 g2: Graph) x root,
      uf_equiv g1 g2 -> vvalid g2 x -> (~ reachable g2 root x) -> uf_root g2 x root -> uf_equiv g1 (pregraph_gen_dst g2 (out_edge x) root).
  Proof.
    intros. apply (@uf_equiv_trans _ _ _ _ g2 _ (liGraph g2) _ (maGraph g2) (finGraph g2)); auto. split; intro y; simpl; [intuition |]. intros.
    assert (Decidable (reachable g2 y x)) by (apply Graph_reachable_dec; left; destruct H3; apply reachable_head_valid in H3; auto).
    apply decidable_prop_decidable in H5. destruct H5.
    - pose proof (uf_root_gen_dst_same g2 (liGraph g2) _ _ _ H2 H1 H5). simpl in H6.
      pose proof (uf_root_unique _ (gen_dst_preserve_lst g2 (liGraph g2) _ _ H1 H0) _ _ _ H4 H6). subst r2.
      pose proof (uf_root_reachable _ _ _ _ H5 H2). apply (uf_root_unique g2 (liGraph g2) _ _ _ H3 H7).
    - apply (uf_root_unique _ (gen_dst_preserve_lst g2 (liGraph g2) _ _ H1 H0) y); auto. apply (uf_root_gen_dst_preserve g2 (liGraph g2)); auto.
  Qed.

  Lemma graph_gen_redirect_parent_equiv: forall (g1 g2: Graph) x r pa root (Hv: vvalid g2 x) (Hn: ~ reachable g2 root x),
      vvalid g1 x -> vgamma g1 x = (r, pa) -> pa <> x -> uf_equiv g1 g2 -> uf_root g2 pa root -> uf_equiv g1 (pregraph_gen_dst g2 (out_edge x) root).
  Proof.
    intros. apply graph_gen_redirect_parent_equiv'; auto. rewrite <- (uf_equiv_root_the_same g1); auto.
    apply (uf_root_edge g1 (liGraph g1) x pa); [| apply (vgamma_not_dst g1 x r) | rewrite (uf_equiv_root_the_same g1 g2)]; auto.
  Qed.

  Lemma graph_gen_redirect_parent_findS: forall (g1 g2: Graph) x r1 r2 pa pa' (H: weak_valid g2 pa') (Hv: vvalid g2 x) (Hn: ~ reachable g2 pa' x),
      vvalid g1 x -> vgamma g1 x = (r1, pa) -> pa <> x -> vgamma g2 x = (r2, pa) -> findS g1 pa g2 -> uf_root g2 pa pa' ->
      findS g1 x (Graph_gen_redirect_parent g2 x pa' H Hv Hn).
  Proof.
    intros. hnf. simpl. destruct H4 as [? [? ?]]. hnf in H4. simpl in H4. unfold predicate_vvalid, predicate_weak_evalid in H4. split; [|split].
    - assert (forall v, ~ reachable (lg_gg g1) x v -> ~ reachable (lg_gg g1) pa v). {
        intros. intro. apply H8. pose proof (gamma_parent_reachable_included g1 x r1 pa H0 H1). apply H10. auto. }
      assert (forall v, ~ reachable (lg_gg g1) pa v <-> ~ reachable (lg_gg g1) x v \/ x = v). {
        intros. split; intros.
        - destruct_eq_dec x v; [right | left]; auto. intro. apply H9. apply reachable_ind.reachable_ind in H11. destruct H11. 1: exfalso; auto.
          destruct H11 as [z [[_ [_ ?]] [? ?]]]. rewrite (dst_step g1 (liGraph g1) x pa) in H11; auto; [subst pa | apply (vgamma_not_dst g1 x r1)]; auto.
        - destruct H9.
          + apply H8; auto.
          + subst v. apply vgamma_not_reachable with r1; auto.
      } hnf. simpl. unfold predicate_vvalid, predicate_weak_evalid. simpl. destruct H4 as [? [? [? ?]]]. split; [|split; [|split]]; intros.
      + split; intros; destruct H13; split; auto; apply H8 in H14; pose proof (conj H13 H14); [rewrite H4 in H15 | rewrite <- H4 in H15]; destruct H15; auto.
      + split; intros; destruct H13.
        * pose proof (H8 _ H14). pose proof (conj H13 H15). rewrite H10 in H16. destruct H16. rewrite H9 in H17. destruct H17. 1: split; auto. symmetry in H17.
          pose proof (conj H17 H16). rewrite (@only_one_edge _ _ _ _ g2 _ (liGraph g2)) in H18; auto. subst e. pose proof (vvalid_src_evalid _ (liGraph g1) _ H0).
          destruct H18 as [? _]. unfold Graph_LGraph in H18. rewrite H18 in H14. exfalso. apply H14. apply reachable_refl. auto.
        * pose proof (H8 _ H14). pose proof (conj H13 H15). rewrite <- H10 in H16. destruct H16. rewrite H9 in H17. destruct H17. 1: split; auto. symmetry in H17.
          pose proof (conj H17 H16). rewrite (@only_one_edge _ _ _ _ g1 _ (liGraph g1)) in H18; auto. subst e. pose proof (vvalid_src_evalid _ (liGraph g2) _ Hv).
          destruct H18 as [? _]. unfold Graph_LGraph in H18. rewrite H18 in H14. exfalso. apply H14. apply reachable_refl. auto.
      + destruct H13, H14. apply H8 in H15. apply H8 in H16. apply H11; auto.
      + unfold updateEdgeFunc. destruct (equiv_dec (out_edge x) e).
        * unfold Equivalence.equiv in e0. subst e. pose proof (vvalid_src_evalid _ (liGraph g1) _ H0).
          destruct H15. unfold Graph_LGraph in H15. destruct H13. exfalso. apply H17. rewrite H15. apply reachable_refl; auto.
        * destruct H13, H14. apply H8 in H15. apply H8 in H16. apply H12; auto.
    - apply (graph_gen_redirect_parent_equiv _ _ _ r1 pa); auto.
    - apply H7.
  Qed.

  Lemma diff_root_union_1: forall (g g1 g2: Graph) x y x_root y_root,
      uf_equiv g g1 -> uf_root g1 x x_root -> uf_equiv g1 g2 -> uf_root g2 y y_root -> x_root <> y_root ->
      (@weak_valid _ _ _ _ g2 _ (maGraph g2) y_root) -> vvalid g2 x_root ->
      ~ reachable g2 y_root x_root -> uf_union g x y (pregraph_gen_dst g2 (out_edge x_root) y_root).
  Proof.
    intros. assert (uf_equiv g g2) by (apply (@uf_equiv_trans _ _ _ _ g1 _ (liGraph g1) _ (maGraph g1) (finGraph g1)); auto).
    pose proof (uf_equiv_union g g2 (Graph_gen_redirect_parent g2 x_root y_root H4 H5 H6) x y H7). simpl in H8. apply H8.
    apply (@diff_root_union _ _ _ _ _ _ _ _ out_edge isNullDec fml); auto. apply (uf_equiv_root_the_same g1); auto.
  Qed.

  Lemma diff_root_union_2: forall (g g1 g2: Graph) x y x_root y_root,
      uf_equiv g g1 -> uf_root g1 x x_root -> uf_equiv g1 g2 -> uf_root g2 y y_root -> x_root <> y_root -> (@weak_valid _ _ _ _ g2 _ (maGraph g2) x_root) -> vvalid g2 y_root ->
      ~ reachable g2 x_root y_root -> uf_union g x y (pregraph_gen_dst g2 (out_edge y_root) x_root).
  Proof.
    intros. assert (uf_equiv g g2) by (apply (@uf_equiv_trans _ _ _ _ g1 _ (liGraph g1) _ (maGraph g1) (finGraph g1)); auto).
    pose proof (uf_equiv_union g g2 (Graph_gen_redirect_parent g2 y_root x_root H4 H5 H6) y x H7). simpl in H8. apply uf_union_sym. apply H8.
    apply (@diff_root_union _ _ _ _ _ _ _ _ out_edge isNullDec fml); auto. apply (uf_equiv_root_the_same g1); auto.
  Qed.

  Lemma graph_gen_redirect_parent_vgamma: forall (g1 g2: Graph) x r pa y (H: weak_valid g1 x) (Hv: vvalid g1 y) (Hn: ~ reachable g1 x y),
      (forall a b, out_edge a = out_edge b -> a = b) -> vgamma g1 x = (r, pa) -> g2 = (Graph_gen_redirect_parent g1 y x H Hv Hn) -> vgamma g2 x = (r, pa).
  Proof.
    intros. rewrite H2. clear H2. unfold vgamma in *. simpl in *. inversion H1. f_equal. unfold updateEdgeFunc.
    destruct (equiv_dec (out_edge y) (out_edge x)); auto. hnf in e. apply H0 in e. subst y. exfalso; apply Hn; apply reachable_refl; auto.
  Qed.

End UnionFindGraph.
