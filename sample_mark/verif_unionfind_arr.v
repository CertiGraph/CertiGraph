Require Import Coq.omega.Omega.
Require Import VST.floyd.proofauto.
Require Import RamifyCoq.lib.List_ext.
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
          LOCAL (temp _subsets (pointer_val_val subsets); temp _x (Vint (Int.repr x)); temp _y (Vint (Int.repr x)))
          SEP   (whole_graph sh g subsets)
  POST [ Tvoid ]
        EX g': Graph,
        PROP (uf_union g x y g')
        LOCAL ()
        SEP (whole_graph sh g' subsets).

Definition Vprog : varspecs := nil.

Definition Gprog : funspecs := mallocN_spec :: makeSet_spec :: find_spec :: union_spec ::nil.

(* Lemma whole_graph_empty: forall sh rt n, 0 <= n -> malloc_compatible n (pointer_val_val rt) -> whole_graph sh (makeSet_discrete_Graph 0) rt = emp. *)
(* Proof. *)
(*   intros. unfold whole_graph, full_graph_at. simpl. unfold graph_vcell_at. simpl. unfold vgamma. simpl. unfold vcell_array_at. unfold SAG_VST. apply pred_ext. *)
(*   - apply exp_left. intro l. Intros. destruct l. 2: exfalso; rewrite <- (H1 z); left; auto. simpl. unfold data_at, field_at. simpl. Intros. *)
(*     unfold at_offset. rewrite data_at_rec_eq. simpl. unfold unfold_reptype. simpl. rewrite array_pred_len_0; auto. *)
(*   - apply (exp_right nil). simpl. apply andp_right; [apply andp_right|]; [apply prop_right_emp ..|]; [intros; intuition | constructor |]. *)
(*     unfold data_at. unfold field_at. apply andp_right. *)
(*     + apply prop_right_emp. apply malloc_compatible_field_compatible. simpl. *)
(*       * unfold malloc_compatible in *. destruct (pointer_val_val rt); auto. destruct H0. split; auto. omega. *)
(*       * unfold legal_alignas_type, nested_pred. simpl. auto. *)
(*       * unfold legal_cosu_type, nested_pred. simpl. auto. *)
(*       * simpl. auto. *)
(*       * simpl. exists 2. simpl. auto. *)
(*     + unfold at_offset. rewrite data_at_rec_eq. simpl. unfold unfold_reptype. simpl. rewrite array_pred_len_0; auto. *)
(* Qed. *)

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
  - split. 1: omega. assert (Z.mul 8 (Int.max_signed /8) <= Int.max_signed) by (apply Z_mult_div_ge; intuition).
    apply Z.le_trans with Int.max_signed. 1: omega. rewrite Z.lt_eq_cases; left; apply Int.max_signed_unsigned.
  - Intro rt. Intros.
    assert (memory_block sh (V * 8) (pointer_val_val rt) = data_at_ sh (tarray vertex_type V) (pointer_val_val rt)). {
      assert (memory_block sh (V * 8) (pointer_val_val rt) = memory_block sh (sizeof (tarray vertex_type V)) (pointer_val_val rt)). {
        simpl sizeof. rewrite Zmax0r. 2: intuition. assert (V * 8 = 8 * V)%Z by omega. rewrite H1. auto.
      } rewrite <- memory_block_data_at_; auto. apply malloc_compatible_field_compatible; auto.
      - unfold malloc_compatible in *. destruct (pointer_val_val rt); auto. destruct H0. split; auto. simpl sizeof. rewrite Zmax0r; intuition.
      - unfold legal_alignas_type, nested_pred. simpl. compute. destruct V; auto. exfalso. destruct H. pose proof (Zlt_neg_0 p). intuition.
      - exists 2. compute. auto.
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
    + Opaque Znth. forward. remember (Znth i (progressive_list (Z.to_nat i) (Z.to_nat V)) (Vundef, Vundef)) as lll. destruct lll. forward.
      assert (0 <= i < Zlength (progressive_list (Z.to_nat i) (Z.to_nat V))) by (split; [|rewrite Zlength_correct, progressive_list_length, Z2Nat.id]; omega).
      rewrite upd_Znth_same, upd_Znth_twice; [|auto ..]. unfold progressive_array, data_at.
      rewrite upd_Znth_progressive_list. 2: rewrite Z2Nat.id; omega. entailer. Transparent Znth.
    + forward. apply (exp_right (makeSet_discrete_Graph (Z.to_nat V))). entailer. apply (exp_right rt). entailer. apply andp_right.
      * apply prop_right. intros. simpl. rewrite makeSet_vvalid. rewrite Z2Nat.id; omega.
      * unfold whole_graph, full_graph_at. simpl. apply (exp_right (Z.to_nat V)). apply andp_right; intros; [apply andp_right; apply prop_right|].
        -- intros. rewrite makeSet_vvalid. intuition.
        -- rewrite Z2Nat.id; omega.
        -- simpl. unfold vcell_array_at, SAG_VST. rewrite map_length, nat_inc_list_length. rewrite Z2Nat.id. 2: intuition.
           assert (map (fun x : Z => vgamma (makeSet_discrete_LabeledGraph (Z.to_nat V)) x) (nat_inc_list (Z.to_nat V)) =
                   map (fun x => (0%nat, x)) (nat_inc_list (Z.to_nat V))). {
             apply list_map_exten. intros. unfold vgamma. simpl. rewrite makeSet_dst. simpl. auto.
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

Lemma Znth_nat_inc_list: forall {A: Type} n (f: Z -> A) i a, 0 <= i < Z.of_nat n -> Znth i (map f (nat_inc_list n)) a = f i.
Proof.
  intros. rewrite Znth_map with (d' := 0); auto. 2: rewrite Zlength_correct, nat_inc_list_length; auto. f_equal. induction n.
  - exfalso. simpl in H. intuition.
  - simpl. assert (0 <= i < Z.of_nat n \/ i = Z.of_nat n). {
      rewrite Nat2Z.inj_succ in H. destruct H. rewrite Z.lt_succ_r, Z.lt_eq_cases in H0. destruct H0; [left | right]; auto.
    } assert (Zlength (nat_inc_list n) = Z.of_nat n) by (rewrite Zlength_correct, nat_inc_list_length; auto). destruct H0.
    + rewrite app_Znth1. 2: rewrite H1; destruct H0; auto. apply IHn; auto.
    + rewrite app_Znth2. 2: rewrite H1; intuition. rewrite H0, H1. replace (Z.of_nat n - Z.of_nat n) with 0 by omega. rewrite Znth_0_cons. auto.
Qed.

Lemma body_find: semax_body Vprog Gprog f_find find_spec.
Proof.
  start_function. rewrite whole_graph_unfold. Intros n. forward.
  - entailer. rewrite Znth_nat_inc_list. 2: rewrite H0; auto. apply prop_right. compute. auto.
  - apply prop_right. rewrite H0. auto.
  - rewrite Znth_nat_inc_list. 2: rewrite H0; auto. unfold vgamma2cdata at 1. unfold vgamma at 1.
    forward_if_tac
      (EX g': Graph, EX rt: Z,
       PROP (uf_equiv g g' /\ uf_root g' i rt)
       LOCAL (temp _p (Vint (Int.repr rt)); temp _subsets (pointer_val_val subsets); temp _i (Vint (Int.repr i)))
       SEP (whole_graph sh g' subsets)).
    + admit.
    + forward. rewrite whole_graph_fold; [|intuition..]. apply (exp_right g). rewrite H2. apply (exp_right i). entailer !.
      split. 1: apply (uf_equiv_refl _  (liGraph g)). destruct (Z_lt_dec (dst (lg_gg g) i) 0).
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
    + Intros g' rt. rewrite <- H0 in H. forward. apply (exp_right g'). entailer !.
      * admit.
      * apply (exp_right rt). entailer !.
Abort.
