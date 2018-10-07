Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.sample_mark.env_unionfind_arr.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.graph_relation.
Require Import RamifyCoq.graph.reachable_computable.
Require Import RamifyCoq.graph.UnionFind.
Require Import RamifyCoq.msl_application.UnionFindGraph.
Require Import RamifyCoq.msl_application.ArrayGraph.
Require Import RamifyCoq.floyd_ext.share.
Require Import RamifyCoq.sample_mark.spatial_array_graph.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.

Local Coercion UGraph_LGraph: Graph >-> LGraph.
Local Identity Coercion ULGraph_LGraph: LGraph >-> UnionFindGraph.LGraph.
Local Identity Coercion LGraph_LabeledGraph: UnionFindGraph.LGraph >-> LabeledGraph.
Local Coercion pg_lg: LabeledGraph >-> PreGraph.
Existing Instances maGraph finGraph liGraph.

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
      PROP (uf_equiv g g' /\ uf_root g' i rt)
      LOCAL (temp ret_temp (Vint (Int.repr rt)))
      SEP (whole_graph sh g' subsets).

Definition union_spec :=
 DECLARE _Union
  WITH sh: wshare, g: Graph, subsets: pointer_val, x: Z, y: Z
  PRE [ _subsets OF (tptr vertex_type), _x OF tint, _y OF tint]
          PROP  (vvalid g x /\ vvalid g y)
          LOCAL (temp _subsets (pointer_val_val subsets); temp _x (Vint (Int.repr x)); temp _y (Vint (Int.repr y)))
          SEP   (whole_graph sh g subsets)
  POST [ Tvoid ]
        EX g': Graph,
        PROP (uf_union g x y g')
        LOCAL ()
        SEP (whole_graph sh g' subsets).

Definition Gprog : funspecs := ltac:(with_library prog [mallocN_spec; makeSet_spec; find_spec; union_spec]).

Fixpoint prog_list_helper (i: nat) (n: nat) : list (val * val) :=
  match n with
  | O => nil
  | S n' => if (le_dec i n') then (Vundef, Vundef) :: prog_list_helper i n'
            else (Vint (Int.repr (Z.of_nat (n'))), Vint (Int.repr 0)) :: prog_list_helper i n'
  end.

Definition progressive_list (i: nat) (n: nat) := rev (prog_list_helper i n).

Lemma progressive_list_repeat: forall n, list_repeat n (Vundef, Vundef) = progressive_list O n.
Proof.
  induction n; unfold progressive_list; simpl; auto. unfold progressive_list in IHn. rewrite <- IHn.
  change ((Vundef, Vundef) :: list_repeat n (Vundef, Vundef)) with (((Vundef, Vundef) :: nil) ++ list_repeat n (Vundef, Vundef)).
  change ((Vundef, Vundef) :: nil) with (list_repeat 1 (Vundef, Vundef)). rewrite !list_repeat_app. rewrite Nat.add_comm. auto.
Qed.

Lemma progressive_list_length: forall i n, length (progressive_list i n) = n.
Proof. intros. unfold progressive_list. rewrite rev_length. induction n; simpl; auto. destruct (le_dec i n); simpl; rewrite IHn; auto. Qed.

Definition progressive_array sh i V rt := data_at sh (tarray vertex_type V) (progressive_list (Z.to_nat i) (Z.to_nat V)) (pointer_val_val rt).

Lemma upd_Znth_twice: forall {A: Type} i (l: list A) v1 v2, 0 <= i < Zlength l -> upd_Znth i (upd_Znth i l v1) v2 = upd_Znth i l v2.
Proof.
  intros. unfold upd_Znth. f_equal; [|f_equal].
  - rewrite sublist0_app1.
    + rewrite sublist_same; auto. rewrite Zlength_sublist; omega.
    + rewrite Zlength_sublist; omega.
  - assert (Zlength (sublist 0 i l) = i) by (rewrite Zlength_sublist; omega). rewrite sublist_app2; rewrite H0. 2: omega.
    assert (i + 1 - i = 1) by omega. rewrite H1. clear H1. rewrite Zlength_app. rewrite H0. rewrite Zlength_cons. unfold Z.succ.
    rewrite Zlength_sublist; [|omega..]. assert (i + (Zlength l - (i + 1) + 1) - i = Zlength l - i) by omega. rewrite H1; clear H1.
    rewrite sublist_1_cons. rewrite sublist_same; [auto | omega |]. rewrite Zlength_sublist; omega.
Qed.

Lemma prog_list_helper_gt: forall i j n, (i >= n)%nat -> (j >= n)%nat -> prog_list_helper i n = prog_list_helper j n.
Proof. intros. revert i j H H0. induction n; intros; simpl; auto. destruct (le_dec i n), (le_dec j n); [exfalso; omega ..|]. f_equal. apply IHn; omega. Qed.

Lemma upd_Znth_progressive_list: forall i V,
    0 <= i < Z.of_nat V -> upd_Znth i (progressive_list (Z.to_nat i) V) (Vint (Int.repr i), Vint (Int.repr 0)) = progressive_list (Z.to_nat (i + 1)) V.
Proof.
  intros. induction V. 1: exfalso; simpl in H; intuition. rewrite Nat2Z.inj_succ in H. unfold Z.succ in H. unfold progressive_list. simpl. destruct (le_dec (Z.to_nat i) V).
  - destruct (le_dec (Z.to_nat (i + 1)) V).
    + simpl. assert (0 <= i < Z.of_nat V) by (apply inj_le in l0; rewrite Z2Nat.id in l0; omega). unfold progressive_list in IHV. rewrite <- IHV; auto.
      rewrite upd_Znth_app1; auto. change (rev (prog_list_helper (Z.to_nat i) V)) with (progressive_list (Z.to_nat i) V).
      rewrite Zlength_correct, progressive_list_length. auto.
    + assert (Z.to_nat (i + 1) > V)%nat by omega. apply inj_gt in H0. rewrite Z2Nat.id in H0. 2: omega. assert (i = Z.of_nat V) by omega. subst i.
      clear IHV l n H0 H. rewrite Nat2Z.id. simpl. rewrite upd_Znth_char.
      * f_equal. change 1 with (Z.of_nat 1). rewrite <- Nat2Z.inj_add, Nat2Z.id. f_equal. apply prog_list_helper_gt; omega.
      * change (rev (prog_list_helper V V)) with (progressive_list V V). rewrite Zlength_correct, progressive_list_length. auto.
  - exfalso. assert (Z.to_nat i > V)%nat by omega. apply inj_gt in H0. rewrite Z2Nat.id in H0; omega.
Qed.

Lemma progressive_nat_inc_list: forall n i, (i >= n)%nat -> map (fun x : Z => (Vint (Int.repr x), Vint (Int.repr 0))) (nat_inc_list n) = progressive_list i n.
Proof.
  induction n; intros; unfold progressive_list in *; simpl; auto. destruct (le_dec i n). 1: exfalso; omega. rewrite map_app. simpl. rewrite <- IHn; intuition.
Qed.

Lemma body_makeSet: semax_body Vprog Gprog f_makeSet makeSet_spec.
Proof.
  start_function. forward_call (sh, Z.mul V 8).
  - assert (Int.min_signed <= 8 <= Int.max_signed) by rep_omega.
    assert (Int.min_signed <= V <= Int.max_signed). {
      split; rewrite Z.le_lteq; left.
      - rep_omega. 
      - apply Z.le_lt_trans with (Int.max_signed / 8); [intuition | apply Z.div_lt; omega].
    } rewrite !Int.signed_repr; auto. split. 1: omega.
    assert (Z.mul 8 (Int.max_signed /8) <= Int.max_signed) by (apply Z_mult_div_ge; intuition). rep_omega.
  - split. 1: omega. assert (Z.mul 8 (Int.max_signed /8) <= Int.max_signed) by (apply Z_mult_div_ge; intuition). rep_omega.
  - Intros rt.
    assert (memory_block sh (V * 8) (pointer_val_val rt) = data_at_ sh (tarray vertex_type V) (pointer_val_val rt)). {
      assert (memory_block sh (V * 8) (pointer_val_val rt) = memory_block sh (sizeof (tarray vertex_type V)) (pointer_val_val rt)). {
        simpl sizeof. rewrite Zmax0r. 2: intuition. assert (V * 8 = 8 * V)%Z by omega. rewrite H1. auto.
      } rewrite <- memory_block_data_at_; auto. apply malloc_compatible_field_compatible; auto.
      unfold malloc_compatible in *. destruct (pointer_val_val rt); auto. destruct H0. split; auto. simpl sizeof. rewrite Zmax0r; intuition.
    } rewrite H1. clear H1.
    assert (data_at_ sh (tarray vertex_type V) (pointer_val_val rt) = data_at sh (tarray vertex_type V) (progressive_list O (Z.to_nat V)) (pointer_val_val rt)). {
      unfold data_at_, field_at_, data_at. assert (default_val (nested_field_type (tarray vertex_type V) []) = list_repeat (Z.to_nat V) (Vundef, Vundef)) by reflexivity.
      rewrite H1. rewrite progressive_list_repeat. auto.
    } rewrite H1. clear H1.
    forward_for_simple_bound V 
      (EX i: Z,
       PROP ()
       LOCAL (temp _subsets (pointer_val_val rt); temp _V (Vint (Int.repr V)))
       SEP (progressive_array sh i V rt)); unfold progressive_array.
    + destruct H. apply Z.le_trans with (Int.max_signed / 8); auto. rewrite Z.lt_eq_cases. left. apply Z_div_lt; intuition.
    + entailer.
    + Opaque Znth. forward. remember (Znth i (progressive_list (Z.to_nat i) (Z.to_nat V))) as lll. destruct lll. forward.
      assert (0 <= i < Zlength (progressive_list (Z.to_nat i) (Z.to_nat V))) by (split; [|rewrite Zlength_correct, progressive_list_length, Z2Nat.id]; omega).
      rewrite upd_Znth_same, upd_Znth_twice; [|auto ..]. unfold progressive_array, data_at.
      rewrite upd_Znth_progressive_list. 2: rewrite Z2Nat.id; omega. entailer. Transparent Znth.
    + forward. Exists (makeSet_discrete_Graph (Z.to_nat V)) rt. entailer!.
      * intros. simpl. rewrite makeSet_vvalid. rewrite Z2Nat.id; omega.
      * unfold whole_graph, full_graph_at. simpl. Exists (Z.to_nat V). apply andp_right; intros; [apply andp_right; apply prop_right|].
        -- intros. rewrite makeSet_vvalid. intuition.
        -- rewrite Z2Nat.id; omega.
        -- simpl. unfold vcell_array_at, SAG_VST. rewrite map_length, nat_inc_list_length. rewrite Z2Nat.id. 2: intuition.
           assert (map (fun x : Z => vgamma (makeSet_discrete_LabeledGraph (Z.to_nat V)) x) (nat_inc_list (Z.to_nat V)) =
                   map (fun x => (0%nat, x)) (nat_inc_list (Z.to_nat V))). {
             apply list_map_exten. intros. unfold vgamma, UnionFindGraph.vgamma. simpl. rewrite makeSet_dst. simpl. auto.
           } rewrite H6. clear H6. rewrite list_map_compose. unfold vgamma2cdata. simpl. rewrite <- progressive_nat_inc_list; intuition. 
Qed.

Lemma whole_graph_fold: forall n sh g p,
    (forall v : Z, 0 <= v < Z.of_nat n <-> vvalid (lg_gg g) v) -> Z.of_nat n <= Int.max_signed / 8 ->
    data_at sh (tarray vertex_type (Z.of_nat n)) (map (fun x : Z => vgamma2cdata (vgamma (lg_gg g) x)) (nat_inc_list n)) (pointer_val_val p) = whole_graph sh g p.
Proof.
  intros. apply pred_ext; unfold whole_graph, full_graph_at, vcell_array_at, SAG_VST; [apply (exp_right n)|Intros n']; rewrite map_length, nat_inc_list_length, list_map_compose.
  - apply andp_right; auto. apply andp_right; apply prop_right; auto.
  - destruct (lt_eq_lt_dec n n') as [[? | ?] | ?]; [exfalso | subst n' | exfalso]; auto.
    + assert (vvalid (lg_gg g) (Z.of_nat n)) by (rewrite <- H1; intuition). rewrite <- H in H3. intuition.
    + assert (vvalid (lg_gg g) (Z.of_nat n')) by (rewrite <- H; intuition). rewrite <- H1 in H3. intuition.
Qed.

Lemma whole_graph_unfold: forall sh g p,
    whole_graph sh g p =
    EX n: nat, !! (forall v : Z, 0 <= v < Z.of_nat n <-> vvalid (lg_gg g) v) && !!(Z.of_nat n <= Int.max_signed / 8) &&
                  (data_at sh (tarray vertex_type (Z.of_nat n)) (map (fun x : Z => vgamma2cdata (vgamma (lg_gg g) x)) (nat_inc_list n)) (pointer_val_val p)).
Proof.
  intros. unfold whole_graph, full_graph_at, vcell_array_at, SAG_VST.
  apply pred_ext; Intros n; apply (exp_right n); apply andp_right; [apply andp_right; apply prop_right| |apply andp_right; apply prop_right|];
    auto; rewrite map_length, nat_inc_list_length, list_map_compose; auto.
Qed.

Lemma Znth_nat_inc_list: forall {A: Type} {d: Inhabitant A} n (f: Z -> A) i, 0 <= i < Z.of_nat n -> Znth i (map f (nat_inc_list n)) = f i.
Proof.
  intros. rewrite Znth_map. 2: rewrite Zlength_correct, nat_inc_list_length; auto. f_equal. induction n.
  - exfalso. simpl in H. intuition.
  - simpl. assert (0 <= i < Z.of_nat n \/ i = Z.of_nat n). {
      rewrite Nat2Z.inj_succ in H. destruct H. rewrite Z.lt_succ_r, Z.lt_eq_cases in H0. destruct H0; [left | right]; auto.
    } assert (Zlength (nat_inc_list n) = Z.of_nat n) by (rewrite Zlength_correct, nat_inc_list_length; auto). destruct H0.
    + rewrite app_Znth1. 2: rewrite H1; destruct H0; auto. apply IHn; auto.
    + rewrite app_Znth2. 2: rewrite H1; intuition. rewrite H0, H1. replace (Z.of_nat n - Z.of_nat n) with 0 by omega. rewrite Znth_0_cons. auto.
Qed.

Lemma graph_same_size: forall (g g': Graph) n n', (forall x : Z, vvalid g x <-> vvalid g' x) -> (forall v : Z, 0 <= v < Z.of_nat n' <-> vvalid (lg_gg g') v) ->
                                                  (forall v : Z, 0 <= v < Z.of_nat n <-> vvalid (lg_gg g) v) -> n = n'.
Proof.
  intros. assert (forall v, 0 <= v < Z.of_nat n' <-> 0 <= v < Z.of_nat n). intros. rewrite H0. rewrite H1. symmetry. apply H. clear -H2.
  destruct (lt_eq_lt_dec n n'); [destruct s|]; auto; exfalso.
  - specialize (H2 (Z.of_nat n)). omega.
  - specialize (H2 (Z.of_nat n')). omega.
Qed.

Lemma list_eq_Znth {A} {d: Inhabitant A}: forall (l1 l2: list A) n, length l1 = n -> length l2 = n -> (forall j, 0 <= j < Z.of_nat n -> Znth j l1 = Znth j l2) -> l1 = l2.
Proof.
  intros l1 l2 n. revert l1 l2. induction n; intros.
  - simpl in *. destruct l1, l2; simpl in *; [auto | exfalso; intuition..].
  - destruct l1, l2; simpl in H, H0; [exfalso; intuition..| ]. assert (a = a0) by (specialize (H1 0); rewrite !Znth_0_cons in H1; apply H1; rewrite Nat2Z.inj_succ; omega).
    subst a0. cut (l1 = l2); intros. 1: subst l2; auto. inversion H. inversion H0. apply (IHn _ _); auto. intros. specialize (H1 (j + 1)).
    assert (0 < j + 1) by omega. assert (j + 1 - 1 = j) by omega. rewrite !Znth_pos_cons in H1; auto. rewrite !H6 in H1. apply H1. rewrite Nat2Z.inj_succ. omega.
Qed.

Lemma upd_Znth_Graph_redirect_parent: forall (i root : Z) (g: Graph) n (Hw: weak_valid g root) (Hv: vvalid g i) (Hi: ~ reachable g root i),
    0 <= i < Z.of_nat n -> 0 <= root < Z.of_nat n -> upd_Znth i (map (fun m : Z => vgamma2cdata (vgamma (lg_gg g) m)) (nat_inc_list n))
                                                              (Vint (Int.repr root), Vint (Int.repr (Z.of_nat (vlabel (lg_gg g) i)))) =
                                                     map (fun m : Z => vgamma2cdata (vgamma (lg_gg (Graph_gen_redirect_parent g i root Hw Hv Hi)) m))(nat_inc_list n).
Proof.
  intros. 
  assert (Zlength (map (fun m : Z => vgamma2cdata (vgamma (lg_gg g) m)) (nat_inc_list n)) = Z.of_nat n) by (rewrite Zlength_map, Zlength_correct, nat_inc_list_length; auto).
  apply (list_eq_Znth _ _ n).
  - rewrite <- (Nat2Z.id n) at 2. rewrite <- Zlength_length. 2: omega. rewrite upd_Znth_Zlength; auto. rewrite <- H1 in H. auto.
  - rewrite list_length_map, nat_inc_list_length; auto.
  - intros. rewrite Znth_nat_inc_list; auto. rewrite (upd_Znth_lookup' (Z.of_nat n)); auto. rewrite Znth_nat_inc_list; auto.
    unfold vgamma2cdata, vgamma, UnionFindGraph.vgamma. simpl. unfold graph_gen.updateEdgeFunc. unfold EquivDec.equiv_dec, Z_EqDec, zeq. destruct (Z.eq_dec j i).
    + subst j. destruct (Z.eq_dec i i). 2: exfalso; apply n0; auto. f_equal. destruct (Z_lt_dec root 0); [exfalso; omega | auto].
    + f_equal. destruct (Z.eq_dec i j). 1: exfalso; intuition. auto.
Qed.

Lemma body_find: semax_body Vprog Gprog f_find find_spec.
Proof.
  start_function. rewrite whole_graph_unfold. Intros n. forward.
  assert (H_BOUND: 0 <= i < Zlength (nat_inc_list n)) by (rewrite Zlength_correct, nat_inc_list_length, H0; assumption). forward.
  - apply prop_right. rewrite H0. auto.
  - rewrite <- (map_id (nat_inc_list n)) at 1. rewrite Znth_nat_inc_list. 2: rewrite H0; auto. simpl id.
    forward_if
      (EX g': Graph, EX rt: Z,
       PROP (uf_equiv g g' /\ uf_root g' i rt)
       LOCAL (temp _p (Vint (Int.repr rt)); temp _subsets (pointer_val_val subsets); temp _i (Vint (Int.repr i)))
       SEP (whole_graph sh g' subsets)).
    + rewrite whole_graph_fold; [|intuition..]. destruct (vgamma (lg_gg g) i) eqn: ?. forward_call (sh, g, subsets, z).
      * unfold vgamma, UnionFindGraph.vgamma in Heqp. inversion Heqp. clear Heqp. destruct (Z_lt_dec (dst (lg_gg g) i) 0). 1: exfalso; apply H2; auto. 
        destruct ((proj2 (@only_one_edge _ _ _ _ _ _ (liGraph g) _ i H)) (eq_refl i)) as [_ ?]. destruct (valid_graph g _ H3) as [_ [? | ?]]; auto.
        hnf in H6. exfalso. apply n1. auto.
      * Intros vret. destruct vret as [g' root]. simpl fst in *. simpl snd in *. rewrite whole_graph_unfold. Intros n'. forward. Opaque Znth. forward. Transparent Znth.
        -- apply prop_right. rewrite H5. destruct H3. rewrite <- H3. auto.
        -- assert (n' = n). {
             destruct H3, (lt_eq_lt_dec n n'); [destruct s|]; auto; exfalso.
             - specialize (H3 (Z.of_nat n)). specialize (H0 (Z.of_nat n)). specialize (H5 (Z.of_nat n)). rewrite <- H0 in H3. rewrite <- H3 in H5. omega.
             - specialize (H3 (Z.of_nat n')). specialize (H0 (Z.of_nat n')). specialize (H5 (Z.of_nat n')). rewrite <- H0 in H3. rewrite <- H3 in H5. omega.
           } subst n'. assert (z <> i) by (unfold vgamma, UnionFindGraph.vgamma in Heqp; inversion Heqp; intro; apply H2; rewrite H9 in H7; rewrite H9; subst i; auto).
           assert (weak_valid g' root) by (right; destruct H4; apply reachable_foot_valid in H4; auto).
           assert (vvalid g' i) by (destruct H3 as [? _]; rewrite <- H3; apply H).
           assert (~ reachable g' root i) by (apply (uf_equiv_not_reachable g g' i n0 z root); auto).
           apply (exp_right (Graph_gen_redirect_parent g' i root H8 H9 H10)). apply (exp_right root). rewrite Znth_nat_inc_list. 2: rewrite H0; auto.
           Opaque vgamma2cdata. Opaque vgamma. entailer !; [split|]. Transparent vgamma. Transparent vgamma2cdata.
           ++ apply (graph_gen_redirect_parent_equiv g g' i n0 z); auto.
           ++ apply (uf_root_gen_dst_same g' (liGraph g') i i root); auto.
              ** rewrite <- (uf_equiv_root_the_same g g' i root); auto.
                 apply (uf_root_edge _ (liGraph g) _ z); [| apply (vgamma_not_dst g i n0 z) | rewrite (uf_equiv_root_the_same g g')]; auto.
              ** apply reachable_refl; auto.
           ++ rewrite whole_graph_unfold. apply (exp_right n). entailer. unfold vgamma2cdata at 2. unfold vgamma at 2. unfold UnionFindGraph.vgamma.
              cut ((upd_Znth i (map (fun x : Z => vgamma2cdata (vgamma (lg_gg g') x)) (nat_inc_list n))
                             (Vint (Int.repr root), Vint (Int.repr (Z.of_nat (vlabel (lg_gg g') i))))) =
                   (map (fun x : Z => vgamma2cdata (vgamma (lg_gg (Graph_gen_redirect_parent g' i root H8 H9 H10)) x)) (nat_inc_list n))); intros.
              ** rewrite <- H15. apply derives_refl.
              ** rewrite <- H0 in H. destruct H4. apply reachable_foot_valid in H4. rewrite <- H5 in H4. clear -H H4. rewrite <- upd_Znth_Graph_redirect_parent; auto.
    + unfold vgamma2cdata at 1. unfold vgamma at 1. unfold UnionFindGraph.vgamma. forward. rewrite whole_graph_fold; [|intuition..]. apply (exp_right g).
      simpl projT2. simpl id. apply (exp_right i). entailer !.
      split; [|split]. 1: apply (uf_equiv_refl _  (liGraph g)). 2: rewrite <- H2; reflexivity. destruct (Z_lt_dec (dst (lg_gg g) i) 0).
      * split. 1: apply reachable_refl; auto. intros. destruct H4 as [[? ?] ?]. destruct H4 as [[? ?] [? ?]]. simpl in H4. subst z. destruct l0.
        -- simpl in H5. auto.
        -- simpl in H6. destruct H6. assert (strong_evalid g z) by (destruct l0; [|destruct H6]; auto). destruct H8 as [? [? ?]]. symmetry in H4.
           destruct (@only_one_edge _ _ _ _ _ _ (liGraph g) _ z H) as [? _]. specialize (H11 (conj H4 H8)). simpl in H11. subst z. rewrite <- H0 in H10.
           destruct H10. assert (dst g i < 0) by apply l. exfalso; omega.
      * destruct (vvalid_src_evalid _ (liGraph g) i H) as [_ ?]. destruct (valid_graph g _ H4) as [_ [? | ?]]. 1: simpl in H5; exfalso; auto. simpl id in *.
        rewrite <- H0 in H5. rewrite <- H0 in H. apply repr_inj_unsigned in H2.
        -- exfalso. rewrite H0 in H. assert (reachable g i i) by (apply reachable_refl; auto). pose proof (dst_not_reachable _ (liGraph g) _ _ _ H H2 H6). auto.
        -- split. 1: omega. rewrite Z.lt_eq_cases. left. apply Z.lt_trans with (Int.max_signed / 8). 2: reflexivity. destruct H5. apply Z.lt_le_trans with (Z.of_nat n); auto. 
        -- split. 1: omega. rewrite Z.lt_eq_cases. left. apply Z.lt_trans with (Int.max_signed / 8). 2: compute; auto. destruct H. apply Z.lt_le_trans with (Z.of_nat n); auto.
    + Intros g' rt. forward. apply (exp_right g'). apply (exp_right rt). entailer !.
Qed.

Lemma bounded_vertex: forall v n, 0 <= v < n -> n <= Int.max_signed / 8 -> Int.min_signed <= v <= Int.max_signed.
Proof.
  intros. destruct H. split.
  - apply Z.le_trans with 0; auto. rewrite Z.lt_eq_cases. left. apply Int.min_signed_neg.
  - apply Z.le_trans with n. 1: rewrite Z.lt_eq_cases; left; auto. apply Z.le_trans with (Int.max_signed / 8); auto. rewrite Z.lt_eq_cases; left. apply Z_div_lt; intuition.
Qed.

Lemma body_union: semax_body Vprog Gprog f_Union union_spec.
Proof.
  start_function. destruct H.
  forward_call (sh, g, subsets, x). Intros vret. destruct vret as [g1 x_root]. simpl fst in *. simpl snd in *.
  assert (vvalid g1 y) by (destruct H1 as [? _]; rewrite <- H1; apply H0).
  forward_call (sh, g1, subsets, y). Intros vret. destruct vret as [g2 y_root]. simpl fst in *. simpl snd in *.
  forward_if
    (PROP (x_root <> y_root)
     LOCAL (temp _yroot (Vint (Int.repr y_root)); temp _xroot (Vint (Int.repr x_root));
     temp _subsets (pointer_val_val subsets); temp _x (Vint (Int.repr x));
     temp _y (Vint (Int.repr y)))  SEP (whole_graph sh g2 subsets)).
  - forward. apply (exp_right g2). entailer. rewrite whole_graph_unfold. Intros n. apply prop_right. apply (the_same_root_union g g1 g2 x y y_root); auto.
    assert (x_root = y_root). {
      assert (Int.signed (Int.repr x_root) = Int.signed (Int.repr y_root)) by (rewrite H6; auto). rewrite !Int.signed_repr in H10; auto.
      - apply (bounded_vertex _ (Z.of_nat n)); auto. destruct H5. apply reachable_foot_valid in H5. rewrite <- H8 in H5; auto.
      - apply (bounded_vertex _ (Z.of_nat n)); auto. destruct H4. destruct H2. apply reachable_foot_valid in H2. rewrite H4 in H2. rewrite <- H8 in H2; auto.
    } subst y_root. apply H2.
  - forward. entailer!.
  - rewrite whole_graph_unfold. Intros n.
    assert (0 <= x_root < Z.of_nat n) by (destruct H4; destruct H2; apply reachable_foot_valid in H2; rewrite H4 in H2; rewrite <- H7 in H2; auto).
    assert (H_XROOT_BOUND: 0 <= x_root < Zlength (nat_inc_list n)) by (rewrite Zlength_correct, nat_inc_list_length; apply H9). forward.
    rewrite <- (map_id (nat_inc_list n)) at 1. rewrite Znth_nat_inc_list; auto. simpl id. unfold vgamma2cdata at 1. unfold vgamma at 1.
    unfold UnionFindGraph.vgamma. assert (0 <= y_root < Z.of_nat n) by (destruct H5; apply reachable_foot_valid in H5; rewrite <- H7 in H5; auto).
    assert (H_YROOT_BOUND: 0 <= y_root < Zlength (nat_inc_list n)) by (rewrite Zlength_correct, nat_inc_list_length; apply H10). forward.
    rewrite <- (map_id (nat_inc_list n)) at 1. rewrite Znth_nat_inc_list; auto. unfold vgamma2cdata at 1. unfold vgamma at 1. unfold UnionFindGraph.vgamma. simpl id.
    forward_if
      (EX g': Graph,
       PROP (uf_union g x y g')
       LOCAL (temp _yRank (Vint (Int.repr (Z.of_nat (vlabel (lg_gg g2) y_root)))); temp _xRank (Vint (Int.repr (Z.of_nat (vlabel (lg_gg g2) x_root))));
              temp _yroot (Vint (Int.repr y_root)); temp _xroot (Vint (Int.repr x_root)); temp _subsets (pointer_val_val subsets); temp _x (Vint (Int.repr x));
              temp _y (Vint (Int.repr y)))
       SEP (whole_graph sh g' subsets)).
    + Opaque Znth. forward. rewrite Znth_nat_inc_list; auto.
      assert (weak_valid g2 y_root) by (right; rewrite <- H7; auto). assert (vvalid g2 x_root) by (rewrite <- H7; auto).
      assert (~ reachable g2 y_root x_root) by (intro; destruct H5; specialize (H15 _ H14); auto).
      apply (exp_right (Graph_gen_redirect_parent g2 x_root y_root H12 H13 H14)). unfold vgamma2cdata at 2. unfold vgamma at 2. unfold UnionFindGraph.vgamma.
      Opaque vgamma2cdata. Opaque vgamma. entailer !. Transparent vgamma. Transparent vgamma2cdata.
      * apply (diff_root_union_1 g g1 g2 x y x_root y_root); auto.
      * rewrite whole_graph_unfold. apply (exp_right n). rewrite <- upd_Znth_Graph_redirect_parent; auto. entailer!.
    + assert (weak_valid g2 x_root) by (right; rewrite <- H7; auto). assert (vvalid g2 y_root) by (rewrite <- H7; auto).
      assert (~ reachable g2 x_root y_root) by (intro; rewrite (uf_equiv_root_the_same g1 g2) in H2; auto; destruct H2; specialize (H15 _ H14); auto).
      forward_if
        (EX g': Graph,
         PROP (uf_union g x y g')
         LOCAL (temp _yRank (Vint (Int.repr (Z.of_nat (vlabel (lg_gg g2) y_root)))); temp _xRank (Vint (Int.repr (Z.of_nat (vlabel (lg_gg g2) x_root)))); 
                temp _yroot (Vint (Int.repr y_root)); temp _xroot (Vint (Int.repr x_root)); temp _subsets (pointer_val_val subsets); temp _x (Vint (Int.repr x));
                temp _y (Vint (Int.repr y)))
         SEP (whole_graph sh g' subsets)).
      * forward. rewrite Znth_nat_inc_list; auto. apply (exp_right (Graph_gen_redirect_parent g2 y_root x_root H12 H13 H14)). unfold vgamma2cdata at 2. unfold vgamma at 2.
        unfold UnionFindGraph.vgamma. Opaque vgamma2cdata. Opaque vgamma. entailer!. Transparent vgamma. Transparent vgamma2cdata.
        -- apply (diff_root_union_2 g g1 g2 x y x_root y_root); auto.
        -- rewrite whole_graph_unfold. apply (exp_right n). rewrite <- upd_Znth_Graph_redirect_parent; auto. entailer!.
      * forward. rewrite Znth_nat_inc_list; auto. remember (Graph_gen_redirect_parent g2 y_root x_root H12 H13 H14) as g3.
        assert (uf_union g x y g3) by (rewrite Heqg3; simpl; apply (diff_root_union_2 g g1 g2 x y x_root y_root); auto).
        unfold vgamma2cdata at 2. unfold vgamma at 2. unfold UnionFindGraph.vgamma. forward. apply (exp_right (Graph_vgen g3 x_root ((vlabel (lg_gg g2) x_root) + 1)%nat)).
        Opaque vgamma2cdata. Opaque vgamma. entailer !. Transparent vgamma. Transparent vgamma2cdata.
        rewrite upd_Znth_diff; auto; [|rewrite Zlength_map, Zlength_correct, nat_inc_list_length; auto..]. rewrite Znth_nat_inc_list; auto.
        rewrite whole_graph_unfold. apply (exp_right n). entailer !.
        cut (upd_Znth x_root (upd_Znth y_root (map (fun x0 : Z => vgamma2cdata (vgamma (lg_gg g2) x0)) (nat_inc_list n))
                                        (Vint (Int.repr x_root), Vint (Int.repr (Z.of_nat (vlabel (lg_gg g2) y_root)))))
                       (let (x0, _) := vgamma2cdata (vgamma (lg_gg g2) x_root) in x0, Vint (Int.repr (Z.of_nat (vlabel (lg_gg g2) x_root) + 1))) =
             map (fun x0 : Z => vgamma2cdata (vgamma (lg_gg (Graph_vgen (Graph_gen_redirect_parent g2 y_root x_root H12 H13 H14) x_root
                                                                        (vlabel (lg_gg g2) x_root + 1)%nat)) x0)) (nat_inc_list n)); intros.
        -- rewrite <- H23. apply derives_refl.
        -- clear -H6 H9 H10. assert (Zlength (map (fun m : Z => vgamma2cdata (vgamma (lg_gg g2) m)) (nat_inc_list n)) = Z.of_nat n) by
               (rewrite Zlength_map, Zlength_correct, nat_inc_list_length; auto).
           assert (Zlength (upd_Znth y_root (map (fun x0 : Z => vgamma2cdata (vgamma (lg_gg g2) x0)) (nat_inc_list n))
                                     (Vint (Int.repr x_root), Vint (Int.repr (Z.of_nat (vlabel (lg_gg g2) y_root))))) = Z.of_nat n) by
               (rewrite upd_Znth_Zlength; auto; rewrite <- H in H10; auto). apply (list_eq_Znth _ _ n).
           ++ rewrite <- (Nat2Z.id n) at 2. rewrite <- Zlength_length. 2: omega. rewrite <- H in H10, H9. rewrite upd_Znth_Zlength; auto; rewrite upd_Znth_Zlength; auto.
           ++ rewrite list_length_map, nat_inc_list_length; auto.
           ++ intros. rewrite Znth_nat_inc_list; auto. rewrite (upd_Znth_lookup' (Z.of_nat n)); auto. rewrite (upd_Znth_lookup' (Z.of_nat n)); auto.
              rewrite Znth_nat_inc_list; auto. unfold vgamma2cdata, vgamma, UnionFindGraph.vgamma. simpl.
              unfold graph_gen.updateEdgeFunc, graph_gen.update_vlabel, EquivDec.equiv_dec, Z_EqDec, zeq. destruct (Z.eq_dec j x_root).
              ** subst j. destruct (Z.eq_dec y_root x_root). 1: exfalso; auto. destruct (Z.eq_dec x_root x_root). 2: exfalso; apply n1; auto. do 3 f_equal.
                 transitivity (Z.succ (Z.of_nat (vlabel (lg_gg g2) x_root))). 2: rewrite <- Nat2Z.inj_succ; f_equal; unfold Z_EqDec; omega. rewrite Z.add_1_r. auto.
              ** destruct (Z.eq_dec j y_root).
                 --- subst j. destruct (Z.eq_dec y_root y_root). 2: exfalso; apply n1; auto. destruct (Z.eq_dec x_root y_root). 1: exfalso; auto. destruct (Z_lt_dec x_root 0).
                     1: destruct H9; exfalso; omega. auto.
                 --- destruct (Z.eq_dec y_root j). 1: exfalso; apply n1; auto. destruct (Z.eq_dec x_root j). 1: exfalso; auto. auto.
    + Intros g'. forward. apply (exp_right g'). entailer!.
Qed.
