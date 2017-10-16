Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.lib.Ensembles_ext.
Require Import RamifyCoq.lib.EnumEnsembles.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.graph_gen.
Require Import RamifyCoq.graph.MathGraph.
Require Import RamifyCoq.graph.LstGraph.
Require Import RamifyCoq.graph.FiniteGraph.
Require Import RamifyCoq.graph.reachable_computable.

Section UNION_FIND_SINGLE.

  Context {Vertex: Type}.

  Definition uf_set := Ensemble Vertex.

  Context {Edge: Type}.
  Context {EV: EqDec Vertex eq}.
  Context {EE: EqDec Edge eq}.

  Definition uf_root (pg: PreGraph Vertex Edge) (x root: Vertex) : Prop := reachable pg x root /\ (forall y, reachable pg root y -> root = y).

  Definition uf_set_in (g: PreGraph Vertex Edge) (s: uf_set) : Prop := (Same_set s (Empty_set Vertex)) \/ (exists rt, s rt /\ forall x, s x <-> uf_root g x rt).

  Definition uf_equiv (g1 g2: PreGraph Vertex Edge) : Prop :=
    (forall x, vvalid g1 x <-> vvalid g2 x) /\ (forall x r1 r2, uf_root g1 x r1 -> uf_root g2 x r2 -> r1 = r2).

  Definition uf_union (g1: PreGraph Vertex Edge) (e1 e2: Vertex) (g2: PreGraph Vertex Edge) : Prop :=
    forall (S1 S2: uf_set), S1 e1 -> S2 e2 -> uf_set_in g1 S1 -> uf_set_in g1 S2 ->
                            uf_set_in g2 (Union Vertex S1 S2) /\ (forall S, ~ Same_set S S1 -> ~ Same_set S S2 -> uf_set_in g1 S -> uf_set_in g2 S) /\
                            (forall S, uf_set_in g2 S -> Same_set S (Union Vertex S1 S2) \/ uf_set_in g1 S).

  Definition uf_bound (g: PreGraph Vertex Edge) (root: Vertex) (h: nat): Prop := forall p, valid_path g p -> pfoot g p = root -> length (snd p) <= h.

  Lemma uf_equiv_sym: forall g1 g2, uf_equiv g1 g2 -> uf_equiv g2 g1.
  Proof. intros. destruct H. split; intros; [specialize (H x); intuition | specialize (H0 x r2 r1); symmetry; apply H0; auto]. Qed.

  Lemma uf_union_sym: forall g1 g2 e1 e2, uf_union g1 e1 e2 g2 -> uf_union g1 e2 e1 g2.
  Proof.
    intros. repeat intro. specialize (H S2 S1 H1 H0 H3 H2). assert (Same_set (Union Vertex S1 S2) (Union Vertex S2 S1)). {
      rewrite Same_set_spec. hnf. intros. split; intro; destruct H4; [right | left | right | left]; auto.
    } destruct H as [? [? ?]]. split; [|split].
    - destruct H; [left; rewrite H4; auto | right]. destruct H as [rt [? ?]]. pose proof (app_same_set H4). exists rt. split; [rewrite H8 | intros; rewrite H8]; auto.
    - intros. apply H5; auto.
    - intros. specialize (H6 _ H7). destruct H6; [left; rewrite H4 | right]; auto.
  Qed.

  Variable (g: PreGraph Vertex Edge).
  Context {out_edge: Vertex -> Edge}.
  Context (gLst: LstGraph g out_edge).

  Lemma uf_root_refl: forall x, vvalid g x -> ~ vvalid g (dst g (out_edge x)) -> uf_root g x x.
  Proof.
    intros. split; intros. 1: apply reachable_refl; auto. destruct H1 as [[? ?] ?]. destruct H1 as [[? ?] [? _]]. simpl in H1. subst v. destruct l. 1: simpl in H2; auto.
    simpl in H3. destruct H3. assert (strong_evalid g e) by (destruct l;[|destruct H3]; auto). clear H3. destruct H4 as [? [? ?]]. symmetry in H1.
    destruct (only_one_edge _ e H) as [? _]. specialize (H6 (conj H1 H3)). subst e. exfalso; auto.
  Qed.    

  Lemma uf_root_unique: forall x r1 r2, uf_root g x r1 -> uf_root g x r2 -> r1 = r2.
  Proof. intros. destruct H, H0. pose proof (lst_reachable_or _ _ _ _ _ H H0). destruct H3; [apply H1 | symmetry; apply H2]; auto. Qed.

  Lemma uf_root_reachable: forall x pa root, reachable g x pa -> uf_root g pa root -> uf_root g x root.
  Proof. intros. destruct H0. split; intros; [apply reachable_trans with pa | apply H1]; auto. Qed.

  Lemma uf_root_reachable2: forall x y root, uf_root g x root -> reachable g y root -> uf_root g y root.
  Proof. intros. apply uf_root_reachable with root; auto. destruct H. split; [apply reachable_refl; apply reachable_foot_valid in H; auto | apply H1]. Qed.

  Lemma uf_root_edge: forall x pa root, vvalid g x -> dst g (out_edge x) = pa -> uf_root g pa root -> uf_root g x root.
  Proof.
    intros. apply (uf_root_reachable x pa); auto. apply reachable_edge with x.
    - apply reachable_refl; auto.
    - hnf. split; [|split]; auto.
      + destruct H1. apply reachable_head_valid in H1. auto.
      + rewrite step_spec. exists (out_edge x). pose proof (vvalid_src_evalid _ _ _ H). destruct H2. split; auto.
  Qed.

  Lemma uf_root_gen_dst: forall x z y root, uf_root g y root -> ~ reachable g y x -> reachable g z x -> uf_root (pregraph_gen_dst g (out_edge x) y) z root.
  Proof.
    intros. assert (vvalid g x) by (apply reachable_foot_valid in H1; auto). assert (vvalid g y) by (destruct H; apply reachable_head_valid in H; auto). split; intros.
    - destruct H1 as [[p l1] ?]. destruct H as [[[q l2] ?] ?]. exists (p, l1 ++ (out_edge x) :: l2).
      assert ((p, l1 ++ (out_edge x) :: l2) = path_glue (p, l1) (x, (out_edge x) :: l2)) by (unfold path_glue; simpl; auto).
      rewrite H5. clear H5. apply reachable_by_path_merge with x.
      + rewrite no_edge_gen_dst_equiv; auto. intro. simpl in H5. apply in_split in H5. destruct H5 as [l3 [l4 ?]]. subst l1.
        assert (paths_meet_at g (p, l3) (x, out_edge x :: l4) x). {
          hnf; split. 2: simpl; auto. destruct H1 as [_ [? _]]. apply pfoot_split in H1. pose proof (vvalid_src_evalid _ _ _ H2). destruct H5. rewrite H5 in H1. auto.
        } assert ((p, l3 ++ out_edge x :: l4) = path_glue (p, l3) (x, (out_edge x) :: l4)) by (unfold path_glue; simpl; auto). rewrite H6 in H1; clear H6.
        apply reachable_by_path_split_glue with (n := x) in H1; auto. clear H5. destruct H1. apply no_loop_path in H5. inversion H5.
      + assert ((x, out_edge x :: l2) = path_glue (x, out_edge x :: nil) (y, l2)) by (unfold path_glue; simpl; auto).
        rewrite H5; clear H5. apply reachable_by_path_merge with y.
        * assert (valid_path (pregraph_gen_dst g (out_edge x) y) (x, out_edge x :: nil)). {
            simpl. unfold strong_evalid. simpl. unfold updateEdgeFunc. destruct (equiv_dec (out_edge x) (out_edge x)). 2: compute in c; exfalso; apply c; auto.
            pose proof (vvalid_src_evalid _ _ _ H2). destruct H5. rewrite H5. split; [|split; [|split]]; auto.
          } split; split; auto.
          -- simpl. unfold updateEdgeFunc. destruct (equiv_dec (out_edge x) (out_edge x)); auto. compute in c; exfalso; apply c; auto.
          -- rewrite path_prop_equiv; auto.
        * assert (q = y) by (destruct H as [[? _] _]; simpl in H; auto). subst q. rewrite no_edge_gen_dst_equiv; auto. intro. simpl in H5.
          apply H0. apply (reachable_path_in g (y, l2) _ root); auto. right; simpl; exists (out_edge x); split; auto; left.
          pose proof (vvalid_src_evalid _ _ _ H2); destruct H6; auto.
    - destruct H. apply H5. rewrite not_reachable_gen_dst_equiv in H4; auto. pose proof (vvalid_src_evalid _ _ _ H2).
      destruct H6. rewrite H6. intro; apply H0. apply reachable_trans with root; auto.
  Qed.

  Lemma uf_root_gen_dst_preserve: forall x y z root, vvalid g x -> ~ reachable g z x -> uf_root g z root -> uf_root (pregraph_gen_dst g (out_edge x) y) z root.
  Proof.
    intros. split; intros.
    - destruct H1 as [[[p l] ?] ?]. assert (p = z) by (destruct H1 as [[? _] _]; simpl in H0; auto). subst p. exists (z, l).
      rewrite no_edge_gen_dst_equiv; auto. simpl. intro. apply H0. apply (reachable_path_in g (z, l) _ root); auto. right; simpl. exists (out_edge x). split; auto; left.
      pose proof (vvalid_src_evalid _ _ _ H). destruct H4; auto.
    - destruct H1. apply H3. rewrite not_reachable_gen_dst_equiv in H2; auto. pose proof (vvalid_src_evalid _ _ _ H). destruct H4. rewrite H4. intro. apply H0.
      apply reachable_trans with root; auto.
  Qed.

  Lemma uf_root_gen_dst_same: forall x y pa, uf_root g x pa -> ~ reachable g pa x -> reachable g y x -> uf_root (pregraph_gen_dst g (out_edge x) pa) y pa.
  Proof. intros. apply uf_root_gen_dst; auto. destruct H. split; [|apply H2]. apply reachable_refl. apply reachable_foot_valid in H; auto. Qed.

  Lemma uf_root_gen_dst_diff: forall x y x_root y_root z,
      uf_root g x x_root -> uf_root g y y_root -> x_root <> y_root -> uf_root g z x_root -> uf_root (pregraph_gen_dst g (out_edge x_root) y_root) z y_root.
  Proof.
    intros. apply uf_root_gen_dst.
    - destruct H0. split; [apply reachable_refl; apply reachable_foot_valid with y; auto | apply H3].
    - intro. apply H1. destruct H0. symmetry. apply H4; auto.
    - destruct H2; auto.
  Qed.

  Lemma uf_root_gen_dst_diff_preserve: forall x y x_root y_root z,
      uf_root g x x_root -> uf_root g y y_root -> x_root <> y_root -> uf_root g z y_root -> uf_root (pregraph_gen_dst g (out_edge x_root) y_root) z y_root.
  Proof.
    intros. apply uf_root_gen_dst_preserve; auto.
    - destruct H. apply reachable_foot_valid in H; auto.
    - intro. apply H1. destruct H2. destruct (lst_reachable_or g _ _ _ _ H3 H2); [destruct H | destruct H0; symmetry]; apply H6; auto.
  Qed.

  Lemma uf_equiv_refl: uf_equiv g g.
  Proof. hnf; split; intros; intuition. destruct H, H0. destruct (@lst_reachable_or _ _ _ _ _ _ gLst _ _ _ H H0); [apply H1 | symmetry; apply H2]; auto. Qed.

  Lemma redirect_to_root: forall x root p l v,
      vvalid g x -> ~ reachable g root x -> (forall y, reachable g root y -> root = y) -> valid_path (pregraph_gen_dst g (out_edge x) root) (p, l) ->
      pfoot (pregraph_gen_dst g (out_edge x) root) (p, l) = v ->
      (valid_path g (p, l) /\ pfoot g (p, l) = v) \/ (v = root /\ exists l1, l = l1 ++ (out_edge x) :: nil /\ g |= (p, l1) is p ~o~> x satisfying (fun _ => True)).
  Proof.
    intros. assert ((pregraph_gen_dst g (out_edge x) root) |= (p, l) is p ~o~> v satisfying (fun _ => True)) by (split; split; auto; rewrite path_prop_equiv; intros; auto).
    destruct (in_dec EE (out_edge x) l). 2: rewrite no_edge_gen_dst_equiv in H4; auto; destruct H4 as [[_ ?] [? _]]; left; auto.
    pose proof (gen_dst_preserve_lst g gLst _ _ H0 H). pose proof (lst_path_NoDup _ H5 _ _ _ _ H4). simpl snd in *. apply in_split in i. destruct i as [l1 [l2 ?]].
    rewrite H7 in H3. rewrite List_ext.app_cons_assoc in H7. rewrite H7 in H2. apply valid_path_app in H2. destruct H2. rewrite pfoot_last in H8.
    rewrite (pfoot_app_cons _ _ root) in H3. rewrite pfoot_cons in H3. simpl dst in *. unfold updateEdgeFunc in *. destruct (equiv_dec (out_edge x) (out_edge x)).
    2: compute in c; exfalso; apply c; auto. rewrite <- List_ext.app_cons_assoc in H7. rewrite H7 in H6. apply NoDup_remove_2 in H6.
    assert ((pregraph_gen_dst g (out_edge x) root) |= (root, l2) is root ~o~> v satisfying (fun _ => True)) by (split; split; auto; rewrite path_prop_equiv; intros; auto).
    assert (~ List.In (out_edge x) l1 /\ ~ List.In (out_edge x) l2) by (split; intro; apply H6; rewrite in_app_iff; [left | right]; auto). clear H6. destruct H10.
    rewrite no_edge_gen_dst_equiv in H9; auto. assert (root = v) by (apply H1; exists (root, l2); auto). subst v. rewrite <- H11 in *. apply no_loop_path in H9.
    inversion H9. subst l2. right. clear H11 H9 H10. pose proof (pfoot_split _ _ _ _ _ H2). simpl src in H3. apply valid_path_app in H2. destruct H2.
    pose proof (@only_one_edge _ _ _ _ _ _ gLst x (out_edge x) H). assert ((out_edge x) = (out_edge x)) by auto.
    rewrite <- H10 in H11. clear H10. destruct H11. rewrite H10 in H3.
    assert ((pregraph_gen_dst g (out_edge x) root) |= (p, l1) is p ~o~> x satisfying (fun _ => True)) by (split; split; auto; rewrite path_prop_equiv; intros; auto).
    rewrite no_edge_gen_dst_equiv in H12; auto. split; [|exists l1; split]; auto.
  Qed.

  Context {is_null: DecidablePred Vertex}.
  Context {MA: MathGraph g is_null}.

  Fixpoint find_list (bound: nat) (v: Vertex) (l: list Edge) : list Edge :=
    let next := (dst g (out_edge v)) in
    if (projT2 is_null) next
    then rev l
    else match bound with
         | O => rev l
         | S n => find_list n next (out_edge v :: l)
         end.

  Lemma valid_path'_find_list: forall bound v l, vvalid g v -> pfoot' g (rev l) v = v -> valid_path' g (rev l) -> valid_path' g (find_list bound v l).
  Proof.
    induction bound; intros.
    - assert (find_list 0 v l = rev l) by (simpl; destruct (projT2 is_null (dst g (out_edge v))); auto; destruct (equiv_dec v (dst g (out_edge v))); auto). rewrite H2. auto.
    - simpl. destruct (projT2 is_null (dst g (out_edge v))); auto.
      assert (vvalid g (dst g (out_edge v)) /\ src g (out_edge v) = v /\ evalid g (out_edge v)). {
        destruct is_null as [is_nullP ?]. simpl in *. pose proof (vvalid_src_evalid _ _ _ H). split; auto.
        destruct H2. destruct MA. apply valid_graph in H3. simpl in *. destruct H3. destruct H4; auto. exfalso; auto.
      } destruct H2 as [? [? ?]]. apply IHbound; auto. 1: simpl; pose proof (pfoot_last g (rev l) (out_edge v) (dst g (out_edge v))); simpl in H5; auto.
      destruct l; simpl in *; auto.
      + unfold strong_evalid. rewrite H3. split; [|split]; auto.
      + remember (rev l) as l'. clear Heql' l. induction l'.
        * simpl in *. split; auto. rewrite H0, H3. split; auto. unfold strong_evalid. rewrite H3. split; auto.
        * rewrite <- app_comm_cons in H0. simpl in H0. destruct (l' +:: e) eqn:? . 1: destruct l'; inversion Heql. rewrite <- Heql in *. clear e0 Heql. specialize (IHl' H0).
          clear H0. simpl in *. destruct ((l' +:: e) +:: out_edge v) eqn:? . 1: destruct l'; inversion Heql0. destruct (l' +:: e) eqn:? . 1: destruct l'; inversion Heql1.
          inversion Heql0. subst e1. destruct H1 as [? [? ?]]. split; [|split]; auto. simpl in Heql0. rewrite Heql0. apply IHl'. auto.
  Qed.

  Definition edge_list_head (l: list Edge) (v: Vertex) :=
    match l with
    | nil => v
    | e :: _ => src g e
    end.

  Lemma find_list_foreside: forall b v l, exists l', find_list b v l = rev l ++ l'.
  Proof.
    induction b; intros; simpl.
    - exists nil. rewrite app_nil_r. destruct (projT2 is_null (dst g (out_edge v))); [|destruct (equiv_dec v (dst g (out_edge v)))]; auto.
    - destruct (projT2 is_null (dst g (out_edge v))); [exists nil; rewrite app_nil_r; auto | ].
      specialize (IHb (dst g (out_edge v)) (out_edge v :: l)). destruct IHb as [l1 ?]. simpl in H. rewrite <- app_assoc in H. exists ((out_edge v :: nil) ++ l1). apply H.
  Qed.

  Lemma valid_path_find_list: forall bound v l, vvalid g v -> pfoot' g (rev l) v = v -> valid_path' g (rev l) -> valid_path g (edge_list_head (rev l) v, find_list bound v l).
  Proof.
    intros. simpl. destruct (find_list_foreside bound v l) as [l' ?]. destruct (find_list bound v l) eqn:? .
    - symmetry in H2. apply app_eq_nil in H2. destruct H2. rewrite H2. simpl; auto.
    - split. 2: rewrite <- Heql0; apply valid_path'_find_list; auto. destruct l.
      + simpl in *. destruct bound; simpl in Heql0.
        * destruct (projT2 is_null (dst g (out_edge v))); inversion Heql0.
        * destruct (projT2 is_null (dst g (out_edge v))). 1: inversion Heql0. destruct (find_list_foreside bound (dst g (out_edge v)) (out_edge v :: nil)) as [l'' ?].
          rewrite Heql0 in H3. simpl in H3. inversion H3. pose proof (vvalid_src_evalid g gLst v H). destruct H4; auto.
      + remember (rev (e0 :: l)) eqn:? . destruct l1. 1: exfalso; simpl in Heql1; destruct (rev l); inversion Heql1. simpl in *. inversion H2. auto.
  Qed.

  Lemma find_list_length: forall b x r l, vvalid g x -> pfoot' g (rev l) x = x -> valid_path' g (rev l) -> r = find_list b x l ->
                                          length r = b + length l \/ forall y, reachable g x y -> In_path g y (edge_list_head (rev l) x, r).
  Proof.
    induction b; intros; simpl in H2.
    - assert (r = rev l) by (destruct (projT2 is_null (dst g (out_edge x))); auto). clear H2. subst r. simpl. left. apply rev_length.
    - destruct ((projT2 is_null (dst g (out_edge x)))).
      + right. intros. rewrite <- H2 in *. clear l H2.
        assert (pfoot g (edge_list_head r x, r) = x) by (destruct r; [simpl in * | rewrite pfoot_head_irrel with (v2 := x); unfold pfoot]; auto). apply pfoot_in in H2.
        apply reachable_ind.reachable_ind in H3. destruct H3. 1: subst y; auto. exfalso. destruct H3 as [z [[? [? ?]] [? ?]]].
        rewrite (dst_step g gLst x (dst g (out_edge x))) in H5; auto. rewrite <- H5 in p. apply reachable_head_valid in H7. apply (valid_not_null g z); auto.
      + specialize (IHb (dst g (out_edge x)) r (out_edge x :: l)).
        assert (vvalid g (dst g (out_edge x))). {
          destruct (vvalid_src_evalid g _ _ H); apply (@valid_graph _ _ _ _ g _ MA) in H4. destruct H4 as [_ ?]. destruct H4; auto. exfalso; auto.
        } specialize (IHb H3). assert (pfoot' g (rev (out_edge x :: l)) (dst g (out_edge x)) = dst g (out_edge x)). {
          simpl; apply (pfoot_last g (rev l) (out_edge x) (dst g (out_edge x))).
        } specialize (IHb H4). assert (valid_path' g (rev (out_edge x :: l))). {
          simpl. clear IHb H2 H4. remember (rev l) as l'. clear l Heql'. revert l' H0 H1. induction l'; intros. simpl in *.
          - hnf. pose proof (vvalid_src_evalid g _ _ H). destruct H2. rewrite H2. split; auto.
          - simpl in H1 |-* . assert (strong_evalid g a) by (destruct l'; [|destruct H1]; auto). destruct (l' +:: out_edge x) eqn:? ; auto. split; auto. destruct l'.
            + clear H2. simpl in H0, Heql. rewrite H0. inversion Heql. subst l. subst e. pose proof (vvalid_src_evalid g _ _ H). destruct H2.
              split; auto. apply IHl'; simpl; auto.
            + simpl in Heql. inversion Heql. subst e0. clear H2. destruct H1 as [? [? ?]]. split; auto. rewrite H6. apply IHl'; auto.
        } specialize (IHb H5 H2). destruct IHb; [left; simpl in H6; intuition | right]. intros. simpl in H6. apply reachable_ind.reachable_ind in H7. destruct H7.
        * subst y. destruct (find_list_foreside b (dst g (out_edge x)) (out_edge x :: l)) as [l' ?]. rewrite <- H2 in H7. simpl in H7. rewrite H7. right. exists (out_edge x).
          simpl. rewrite <- app_assoc. rewrite in_app_iff. simpl. split. 1: right; left; auto. left. pose proof (vvalid_src_evalid g _ _ H). destruct H8; auto.
        * destruct H7 as [z [[_ [_ ?]] [_ ?]]]. rewrite (dst_step g gLst x (dst g (out_edge x))) in H7; auto. rewrite H7 in H8. specialize (H6 _ H8).
          assert (edge_list_head (rev l +:: out_edge x) (dst g (out_edge x)) = edge_list_head (rev l) x). {
            remember (rev l ) as l'. destruct l'; simpl; auto. pose proof (vvalid_src_evalid g _ _ H); destruct H9; auto.
          } rewrite H9 in H6. auto.
  Qed.

  Lemma uf_root_always_exists: forall x, EnumCovered Edge (evalid g) -> vvalid g x -> exists root, uf_root g x root.
  Proof.
    intros. remember (find_list (length (proj1_sig X)) x nil). remember (pfoot g (x, l)) as r. exists r.
    assert (valid_path g (x, l)) by (rewrite Heql; change x with (edge_list_head nil x); apply valid_path_find_list; simpl; auto). split; auto.
    - apply (reachable_path_in' g (x, l) x); [|left; simpl; auto]. split; split; auto. rewrite path_prop_equiv; intros; auto.
    - intros. apply reachable_ind.reachable_ind in H1. destruct H1; auto. assert (pfoot' g (rev nil) x = x) by (simpl; auto). assert (valid_path' g (rev nil)) by (simpl; auto).
      pose proof (find_list_length (length (proj1_sig X)) x l nil H H2 H3 Heql). clear H2 H3. rename H4 into H2. simpl in H2. rewrite PeanoNat.Nat.add_0_r in H2.
      destruct H1 as [z [? [? ?]]]. destruct H1 as [? [? ?]]. rewrite step_spec in H6. destruct H6 as [e [? [? ?]]].
      assert (g |= (r, e :: nil) is r ~o~> z satisfying (fun _ => True)) by
          (split; split; simpl; auto; [unfold strong_evalid; rewrite H7, H8; intuition | hnf; rewrite Forall_forall; intros; auto]). exfalso.
      assert (g |= (x, l) is x ~o~> r satisfying (fun _ => True)) by (split; split; [| | | rewrite path_prop_equiv]; auto).
      assert (g |= (x, l +:: e) is x ~o~> z satisfying (fun _ => True)). {
        pose proof (reachable_by_path_merge _ _ _ _ _ _ _ H10 H9). unfold path_glue in H11. simpl in H11. auto. } destruct H2.
      + destruct X as [li [? ?]]. simpl in Heql, H2. unfold In in i. pose proof (lst_path_NoDup _ _ _ _ _ _ H11). simpl in H12. assert (incl (l +:: e) li) by
            (repeat intro; apply i; rewrite in_app_iff in H13; destruct H13 as [? | [? | ?]]; [apply (valid_path_evalid g x) in H13 | subst a | exfalso]; auto).
        pose proof (NoDup_incl_length H12 H13). rewrite app_length in H14. simpl in H14. intuition.
      + assert (In_path g z (x, l)) by (apply H2; exists (x, l +:: e); auto). pose proof (reachable_path_in' _ _ _ _ H10 _ H12). destruct H13 as [[v li] ?].
        assert (g |= (v, li +:: e) is z ~o~> z satisfying (fun _ => True)). {
          pose proof (reachable_by_path_merge _ _ _ _ _ _ _ H13 H9). unfold path_glue in H14. simpl in H14; auto.
        } apply no_loop_path in H14. inversion H14. destruct li; inversion H17.
  Qed.

  Context {FIN: FiniteGraph g}.

  Lemma uf_equiv_uf_root: forall (g': PreGraph Vertex Edge) x root, uf_equiv g' g -> uf_root g' x root -> uf_root g x root.
  Proof.
    intros. destruct H. assert (exists r, uf_root g x r). {
      apply uf_root_always_exists; [apply Enumerable_is_EnumCovered, finiteE | rewrite <- H; destruct H0; apply reachable_head_valid in H0; auto].
    } destruct H2. specialize (H1 _ _ _ H0 H2). subst x0; auto.
  Qed.

  Lemma uf_equiv_trans: forall g1 g2, uf_equiv g1 g -> uf_equiv g g2 -> uf_equiv g1 g2.
  Proof.
    intros. split; intros.
    - destruct H, H0. rewrite <- H0. apply H.
    - pose proof (uf_equiv_uf_root _ _ _ H H1). destruct H0. apply (H4 x); auto.
  Qed.

End UNION_FIND_SINGLE.

Class FML_General (Vertex : Type) (Edge : Type) {EV : EqDec Vertex eq} {EE: EqDec Edge eq} (DV: Type) (DE: Type) (DG: Type)
      (P: LabeledGraph Vertex Edge DV DE DG -> Type) (out_edge: Vertex -> Edge) (is_null: DecidablePred Vertex) :={
    P_Lst: forall g, P g -> LstGraph (pg_lg g) out_edge;
    P_Math: forall g, P g -> MathGraph (pg_lg g) is_null;
    P_Finite: forall g, P g -> FiniteGraph (pg_lg g);
  }.

Section UNION_FIND_GENERAL.

  Context {Vertex: Type}.
  Context {Edge: Type}.
  Context {EV: EqDec Vertex eq}.
  Context {EE: EqDec Edge eq}.
  Context {DV DE DG: Type}.
  Context {P: LabeledGraph Vertex Edge DV DE DG -> Type}.

  Notation Graph := (GeneralGraph Vertex Edge DV DE DG P).
  Local Coercion pg_lg : LabeledGraph >-> PreGraph.
  Local Coercion lg_gg : GeneralGraph >-> LabeledGraph.

  Definition rank_unchanged (g1 g2: Graph) : Prop := forall v, vvalid g1 v -> vvalid g2 v -> vlabel g1 v = vlabel g2 v.

  Definition findS (g1: Graph) (x: Vertex) (g2: Graph) :=
    (predicate_partialgraph g1 (fun n => ~ reachable g1 x n)) ~=~ (predicate_partialgraph g2 (fun n => ~ reachable g1 x n)) /\ uf_equiv g1 g2 /\ rank_unchanged g1 g2.

  Context {out_edge: Vertex -> Edge}.
  Context {is_null: DecidablePred Vertex}.
  Context {fml: FML_General Vertex Edge DV DE DG P out_edge is_null}.

  Definition uf_under_bound (extract: DV -> nat) (g: Graph) : Prop := forall v, vvalid g v -> uf_bound g v (extract (vlabel g v)).

  Lemma uf_equiv_the_same_root: forall (g1 g2: Graph) x root, uf_equiv g1 g2 -> uf_root g1 x root <-> uf_root g2 x root.
  Proof.
    intros. split.
    - specialize (P_Lst g2 (sound_gg g2)). specialize (P_Math g2 (sound_gg g2)). specialize (P_Finite g2 (sound_gg g2)); intros.
      apply (@uf_equiv_uf_root _ _ _ _ g2 out_edge _ is_null _ _ g1); auto.
    - apply uf_equiv_sym in H. specialize (P_Lst g1 (sound_gg g1)). specialize (P_Math g1 (sound_gg g1)). specialize (P_Finite g1 (sound_gg g1)); intros.
      apply (@uf_equiv_uf_root _ _ _ _ g1 out_edge _ is_null _ _ g2); auto.
  Qed.

  Lemma uf_equiv_uf_set_in: forall (g1 g2: Graph) s, uf_equiv g1 g2 -> uf_set_in g1 s -> uf_set_in g2 s.
  Proof. intros. destruct H0; [left | right]; auto. destruct H0 as [rt [? ?]]. exists rt. split; auto. intros. rewrite H1. apply uf_equiv_the_same_root; auto. Qed.

  Lemma uf_set_in_equiv: forall (g1 g2: Graph) s, uf_equiv g1 g2 -> uf_set_in g1 s <-> uf_set_in g2 s.
  Proof. intros. split; apply uf_equiv_uf_set_in; [|apply uf_equiv_sym]; auto. Qed.

  Lemma uf_union_refl: forall (g: Graph) x y root, uf_root g x root -> uf_root g y root -> uf_union g x y g.
  Proof.
    intros. split; [|split]; intros; auto. unfold uf_set_in in *. destruct H3, H4.
    - left. rewrite H3. rewrite H4. rewrite Union_Empty_left. reflexivity.
    - pose proof (app_same_set H3). rewrite H5 in H1. inversion H1.
    - pose proof (app_same_set H4). rewrite H5 in H2. inversion H2.
    - destruct H3 as [rt1 [? ?]]. destruct H4 as [rt2 [? ?]]. assert (rt1 = root). {
        rewrite H5 in H1. apply (@uf_root_unique _ _ _ _ g _ (P_Lst g (sound_gg g)) x); auto.
      } subst rt1. assert (rt2 = root) by (rewrite H6 in H2; apply (@uf_root_unique _ _ _ _ g _ (P_Lst g (sound_gg g)) y); auto).
      subst rt2. right. exists root. split. 1: apply Union_introl; unfold In; auto. intro z. rewrite Union_spec. rewrite H5, H6. intuition.
  Qed.

  Lemma uf_equiv_union: forall (g1 g2 g: Graph) x y, uf_equiv g1 g2 -> uf_union g2 x y g -> uf_union g1 x y g.
  Proof.
    repeat intro. specialize (H0 S1 S2 H1 H2). rewrite (uf_set_in_equiv g1 g2 _ H) in H3. rewrite (uf_set_in_equiv g1 g2 _ H) in H4. specialize (H0 H3 H4).
    destruct H0 as [? [? ?]]. split; [|split]; intros; auto.
    - rewrite (uf_set_in_equiv g1 g2 _ H) in H9. apply H5; auto.
    - specialize (H6 _ H7). destruct H6; [left | right; rewrite (uf_set_in_equiv g1 g2 _ H)]; auto.
  Qed.

  Lemma uf_equiv_union_equiv: forall (g1 g2 g: Graph) x y, uf_equiv g1 g2 -> uf_union g1 x y g <-> uf_union g2 x y g.
  Proof. intros. split; intro; [apply (uf_equiv_union g2 g1); auto; apply uf_equiv_sym | apply (uf_equiv_union g1 g2)]; auto. Qed.

  Lemma same_root_union: forall (g g1 g2: Graph) x y root, uf_equiv g g1 -> uf_equiv g1 g2 -> uf_root g1 x root -> uf_root g2 y root -> uf_union g x y g2.
  Proof.
    intros. assert (uf_equiv g g2). {
      specialize (P_Lst g1 (sound_gg g1)). specialize (P_Math g1 (sound_gg g1)). specialize (P_Finite g1 (sound_gg g1)); intros.
      apply (@uf_equiv_trans _ _ _ _ g1 out_edge _ is_null _ _ g g2); auto.
    } rewrite (uf_equiv_union_equiv g g2 g2); auto. apply uf_union_refl with root; auto. rewrite <- (uf_equiv_the_same_root g1); auto.
  Qed.

  Lemma gen_dst_uf_root: forall (g: Graph) x y z root,
      vvalid g x -> ~ reachable g root x -> uf_root (pregraph_gen_dst g (out_edge x) y) z root -> reachable g z x \/ uf_root g z root.
  Proof.
    intros. assert (vvalid g z) by (destruct H1; apply reachable_head_valid in H1; simpl in H1; auto).
    assert (forall w, {reachable g z w} + {~ reachable g z w}). {
      apply (@reachable_decidable_prime _ _ _ _ g is_null); auto;
        [exact (P_Math g (sound_gg g)) | apply LocalFiniteGraph_FiniteGraph | apply FiniteGraph_EnumCovered]; exact (P_Finite g (sound_gg g)).
    } destruct (X x); [left; auto | right]. destruct H1. pose proof (P_Lst g (sound_gg g)). pose proof (vvalid_src_evalid g _ _ H). destruct H5 as [? _]. split.
    - rewrite not_reachable_gen_dst_equiv in H1; auto. rewrite H5; auto.
    - intro w. intros. apply H3. rewrite not_reachable_gen_dst_equiv; auto. rewrite H5; auto.
  Qed.

  Lemma diff_root_union: forall (g: Graph) x y x_root y_root,
      uf_root g x x_root -> uf_root g y y_root -> x_root <> y_root -> uf_union g x y (pregraph_gen_dst g (out_edge x_root) y_root).
  Proof.
    repeat intro. destruct H4; [pose proof (app_same_set H4); rewrite H6 in H2; inversion H2 |]. destruct H5; [pose proof (app_same_set H5); rewrite H6 in H3; inversion H3 |].
    pose proof (P_Lst g (sound_gg g)). rename H6 into gLst.
    destruct H4 as [rt1 [? ?]]. assert (rt1 = x_root) by (rewrite H6 in H2; apply (@uf_root_unique _ _ _ _ g _ gLst x); auto). subst rt1.
    destruct H5 as [rt2 [? ?]]. assert (rt2 = y_root) by (rewrite H7 in H3; apply (@uf_root_unique _ _ _ _ g _ gLst y); auto). subst rt2.
    assert (forall z, Union Vertex S1 S2 z <-> uf_root (pregraph_gen_dst g (out_edge x_root) y_root) z y_root). {
      intro z; split; intro.
      - inversion H8; subst x0; unfold In in H9.
        + rewrite H6 in H9. apply (uf_root_gen_dst_diff _ gLst x y); auto.
        + rewrite H7 in H9. apply (uf_root_gen_dst_diff_preserve _ gLst x y); auto.
      - assert (~ reachable g y_root x_root) by (intro; apply H1; symmetry; destruct H0; apply H10; auto).
        assert (vvalid g x_root) by (destruct H; apply reachable_foot_valid in H; auto). apply gen_dst_uf_root in H8; auto. destruct H8; [left | right; rewrite H7; auto].
        rewrite H6. split; auto. destruct H. apply H11.
    } assert (vvalid g x_root) by (destruct H; apply reachable_foot_valid in H; auto).
    assert (LstGraph (pregraph_gen_dst g (out_edge x_root) y_root) out_edge). apply gen_dst_preserve_lst; auto; intro; apply H1; destruct H0; symmetry. apply H11; auto.
    split; [|split]; intros.
    - right. exists y_root. split. 1: apply Union_intror; unfold In; auto. apply H8.
    - unfold uf_set_in in *. destruct H13; [left | right]; auto. destruct H13 as [rt [? ?]]. exists rt; split; auto. intro z. rewrite H14.
      assert (forall m, uf_root g m rt -> ~ reachable g m x_root). {
        repeat intro. pose proof (uf_root_reachable2 _ _ _ _ H H16). pose proof (uf_root_unique g gLst _ _ _ H15 H17). subst rt. clear H17 H16. apply H11.
        rewrite Same_set_spec. hnf. intro. rewrite H14. rewrite H6. intuition.
      } split; intro.
      + apply uf_root_gen_dst_preserve; auto.
      + pose proof H16. apply gen_dst_uf_root in H16; auto. 2: apply H15; rewrite H14 in H13; auto. destruct H16; auto. exfalso. pose proof (uf_root_reachable2 _ _ _ _ H H16).
        assert (uf_root (pregraph_gen_dst g (out_edge x_root) y_root) z y_root) by (apply (uf_root_gen_dst_diff _ gLst x y); auto).
        pose proof (uf_root_unique _ H10 _ _ _ H17 H19). subst rt. clear H18 H19. apply H12. rewrite Same_set_spec. hnf. intro. rewrite H14. rewrite H7. intuition.
    - unfold uf_set_in in H11. destruct H11. 1: right; left; auto. destruct H11 as [rt [? ?]]. destruct_eq_dec rt y_root; [left | right].
      + subst rt. rewrite Same_set_spec. hnf. intro z. rewrite H8, H12. intuition.
      + right. exists rt. split; auto. intro z. rewrite H12.
        assert (forall m, uf_root (pregraph_gen_dst g (out_edge x_root) y_root) m rt -> ~ reachable g m x_root). {
          repeat intro. pose proof (uf_root_reachable2 _ _ _ _ H H15). pose proof (uf_root_gen_dst_diff g gLst _ _ _ _ _ H H0 H1 H16).
          pose proof (uf_root_unique _ H10 _ _ _ H14 H17). auto.
        } split; intro.
        * pose proof H15. apply gen_dst_uf_root in H15; auto. 2: rewrite H12 in H11; apply H14; auto. destruct H15; auto. exfalso. apply H14 in H16. auto.
        * apply uf_root_gen_dst_preserve; auto. intro. pose proof (uf_root_reachable2 _ _ _ _ H H16). pose proof (uf_root_unique g gLst _ _ _ H15 H17). subst rt.
          clear H14 H16 H17. rewrite H12 in H11. assert (uf_root g x_root x_root) by (destruct H; split; [apply reachable_refl | apply H14]; auto).
          pose proof (uf_root_gen_dst_diff g gLst _ _ _ _ _ H H0 H1 H14). pose proof (uf_root_unique _ H10 _ _ _ H11 H16). auto.
  Qed.

End UNION_FIND_GENERAL.
