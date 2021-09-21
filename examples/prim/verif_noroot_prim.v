Require Import CertiGraph.prim.prim_env.
Require Export CertiGraph.lib.find_lemmas.
Require Export CertiGraph.priq.is_empty_lemmas.
Require Import CertiGraph.graph.MathUAdjMatGraph. 
Require Import CertiGraph.prim.prim_constants.
Require Import CertiGraph.graph.SpaceUAdjMatGraph3.
Require Import CertiGraph.prim.noroot_prim_spec.

Local Open Scope Z.

(***********************VERIFICATION***********************)

Section NoRootPrimProof.

Context {Z_EqDec : EquivDec.EqDec Z eq}.
Definition addresses := @nil val.

(* A little helper *)
(* TODO: find a better home for this *)
Lemma find_min_lt_inf: forall u l,
    u = find l (fold_right Z.min (hd 0 l) l) 0 -> (@isEmpty inf l) = Vzero ->
    Zlength l > 0 -> Znth u l < inf + 1.
Proof.
  intros. rewrite <- isEmpty_in' in H0. destruct H0 as [? [? ?]].
  rewrite H. rewrite Znth_find.
  - pose proof (fold_min _ _ H0). lia.
  - now apply fold_min_in_list.
Qed.

(**Initialisation functions**)

Lemma body_getCell: semax_body Vprog Gprog f_getCell getCell_spec.
Proof.
  start_function.
  rewrite (SpaceAdjMatGraph_unfold' _ _ _ addresses u); trivial.
  assert ((Zlength (map Int.repr (Znth u (@graph_to_symm_mat size g)))) = size). {
    unfold graph_to_symm_mat, graph_to_mat, vert_to_list.
    rewrite Znth_map; repeat rewrite Zlength_map.
    all: rewrite nat_inc_list_Zlength, Z2Nat.id; lia.
  }
  assert (0 <= i < Zlength (map Int.repr (Znth u (@graph_to_symm_mat size g)))) by lia.
  assert (0 <= i < Zlength (Znth u (@graph_to_symm_mat size g))). {
    rewrite Zlength_map in H1. lia.
  }

  Intros.
  freeze FR := (iter_sepcon _ _) (iter_sepcon _ _).
  unfold list_rep.
  
  assert_PROP (force_val
                 (sem_add_ptr_int
                    tint
                    Signed
                    (force_val
                       (sem_add_ptr_int
                          (tarray tint size)
                          Signed
                          (pointer_val_val graph_ptr)
                          (Vint (Int.repr u))))
                    (Vint (Int.repr i))) =
               field_address
                 (tarray tint size)
                 [ArraySubsc i]
                 (@list_address
                    size
                    CompSpecs
                    (pointer_val_val graph_ptr)
                    u)). {
    entailer!.
    unfold list_address. simpl.
    rewrite field_address_offset.
    1: { rewrite offset_offset_val; simpl; f_equal.
         rewrite Z.add_0_l. f_equal. lia. }            
    destruct H5 as [? [? [? [? ?]]]]. 
    unfold field_compatible; split3; [| | split3]; simpl; auto.
  }
  forward. forward. 
  thaw FR.
  rewrite (SpaceAdjMatGraph_unfold' _ _ _ addresses u); trivial.
  entailer!.
Qed.

Lemma body_initialise_list: semax_body Vprog Gprog f_initialise_list initialise_list_spec.
Proof.
start_function.
assert_PROP(Zlength old_list = size). entailer!.
forward_for_simple_bound size
    (EX i : Z,
     PROP ()
     LOCAL (temp _list arr; temp _a (Vint (Int.repr a)))
     SEP (
      data_at Tsh (tarray tint size) (repeat (Vint (Int.repr a)) (Z.to_nat i) ++(sublist i size old_list)) arr
    ))%assert.
entailer!. rewrite app_nil_l. rewrite sublist_same by lia. entailer!.
(*loop*)
forward. entailer!.
rewrite (sublist_split i (i+1)) by lia.
replace (sublist i (i+1) old_list) with [Znth i old_list]. simpl.
rewrite upd_Znth_char.
rewrite <- repeat_app' by lia.
rewrite <- app_assoc. simpl. auto.
apply Zlength_repeat; lia.
symmetry; apply sublist_one; lia.
(*postcon*)
entailer!. rewrite sublist_nil. rewrite app_nil_r. entailer!.
Qed.

Lemma body_initialise_matrix: semax_body Vprog Gprog f_initialise_matrix initialise_matrix_spec.
Proof.
start_function. rename H3 into Hptrofs1.
assert (HZlength_nat_inc_list: size = Zlength (nat_inc_list (Datatypes.length old_contents))).
rewrite nat_inc_list_Zlength. rewrite <- Zlength_correct. lia.
forward_for_simple_bound size
    (EX i : Z,
     PROP ()
     LOCAL (temp _graph arr; temp _a (Vint (Int.repr a)))
     SEP (
      iter_sepcon.iter_sepcon (fun i => data_at Tsh (tarray tint size) (repeat (Vint (Int.repr a)) (Z.to_nat size)) ((@list_address size CompSpecs arr i)))
        (sublist 0 i (nat_inc_list (Z.to_nat (Zlength old_contents))));
      iter_sepcon.iter_sepcon ((@list_rep size CompSpecs Tsh arr old_contents))
        (sublist i size (nat_inc_list (Z.to_nat (Zlength old_contents))))
    ))%assert.
rewrite (SpaceAdjMatGraph_unfold' _ _ _ addresses 0); trivial.
2: lia.
rewrite H. entailer!.
replace (@list_rep size CompSpecs Tsh arr old_contents 0) with (iter_sepcon.iter_sepcon (@list_rep size CompSpecs Tsh arr old_contents) [0]).
2: { simpl. rewrite sepcon_emp. auto. }
rewrite <- iter_sepcon.iter_sepcon_app.
simpl. entailer!.
rewrite (sublist_split 0 1), (sublist_one 0 1), nat_inc_list_i. simpl; auto.
all: try lia.
rewrite nat_inc_list_Zlength, Z2Nat.id; lia.
rewrite nat_inc_list_Zlength, Z2Nat.id; lia.
(*inner loop*)
replace (sublist i size (nat_inc_list (Z.to_nat (Zlength old_contents))))
  with ([i]++sublist (i+1) size (nat_inc_list (Z.to_nat (Zlength old_contents)))).
2: { rewrite (sublist_split i (i+1)). rewrite (sublist_one i). rewrite nat_inc_list_i; auto.
rewrite Z2Nat.id; lia. lia. rewrite nat_inc_list_Zlength, Z2Nat.id; lia. lia. lia. rewrite nat_inc_list_Zlength, Z2Nat.id; lia. }
rewrite iter_sepcon.iter_sepcon_app. Intros.
forward_for_simple_bound size
    (EX j : Z,
     PROP ()
     LOCAL (temp _i (Vint (Int.repr i)); temp _graph arr; temp _a (Vint (Int.repr a)))
     SEP (
      iter_sepcon.iter_sepcon (fun i => data_at Tsh (tarray tint size) (repeat (Vint (Int.repr a)) (Z.to_nat size)) (@list_address size CompSpecs arr i))
        (sublist 0 i (nat_inc_list (Z.to_nat (Zlength old_contents))));
      data_at Tsh (tarray tint size) (repeat (Vint (Int.repr a)) (Z.to_nat j) ++sublist j size (map (fun x => Vint (Int.repr x)) (Znth i old_contents))) (@list_address size CompSpecs arr i);
      iter_sepcon.iter_sepcon (@list_rep size CompSpecs Tsh arr old_contents)
        (sublist (i+1) size (nat_inc_list (Z.to_nat (Zlength old_contents))))
    ))%assert.
entailer!. simpl. rewrite sepcon_emp. unfold list_rep. rewrite sublist_same. rewrite map_map. entailer!.
auto. rewrite Zlength_map. symmetry; apply H0. apply Znth_In; lia.
(*inner loop body*)
rename i0 into j. unfold list_address.
assert (Zlength (map (fun x => Vint (Int.repr x)) (Znth i old_contents)) = size).
rewrite Zlength_map. apply H0. apply Znth_In; lia.
assert_PROP (field_compatible (tarray tint size) [ArraySubsc j] (offset_val (i * sizeof (tarray tint size)) arr)). entailer!.
assert_PROP(force_val (sem_add_ptr_int tint Signed (force_val (sem_add_ptr_int (tarray tint size) Signed arr (Vint (Int.repr i))))
 (Vint (Int.repr j))) = (field_address (tarray tint size) [ArraySubsc j] (offset_val (i * sizeof (tarray tint size)) arr))). {
  entailer!. symmetry; rewrite field_address_offset. simpl. unfold offset_val.
  destruct arr; simpl; auto.
  rewrite Ptrofs.add_assoc.
  rewrite Zmax0r by lia.
  rewrite (Ptrofs.add_signed (Ptrofs.repr (i * (4 * size)))).
  - rewrite Ptrofs.signed_repr.
    rewrite Ptrofs.signed_repr.
    rewrite Z.add_0_l.
    rewrite Z.mul_comm.
    auto.
    rewrite Z.add_0_l.
    all: split; try rep_lia.
    ++apply (Z.le_trans _ (1*(4*size))). lia.
      apply (Z.le_trans _ (size*(4*size))). apply Z.mul_le_mono_nonneg_r; lia. lia.
    ++apply (Z.le_trans _ (size*(4*size))). apply Z.mul_le_mono_nonneg_r; lia. lia.
  - auto.
}
(*g[i][j] = a*)
forward.
unfold list_address.
replace (upd_Znth j (repeat (Vint (Int.repr a)) (Z.to_nat j) ++ sublist j size (map (fun x => Vint (Int.repr x)) (Znth i old_contents))) (Vint (Int.repr a)))
with (repeat (Vint (Int.repr a)) (Z.to_nat (j + 1)) ++ sublist (j + 1) size (map (fun x => Vint (Int.repr x)) (Znth i old_contents))).
entailer!.
rewrite <- repeat_app' by lia. rewrite <- app_assoc. rewrite upd_Znth_app2.
rewrite Zlength_repeat by lia. rewrite Z.sub_diag by lia.
rewrite (sublist_split j (j+1)) by lia. rewrite (sublist_one j (j+1)) by lia. simpl. rewrite upd_Znth0 by lia. auto.
rewrite Zlength_repeat by lia. rewrite Zlength_sublist; lia.
(*inner loop postcon*)
entailer!.
rewrite (sublist_split 0 i (i+1)) by lia. rewrite (sublist_one i (i+1)) by lia. rewrite nat_inc_list_i.
rewrite iter_sepcon.iter_sepcon_app. rewrite sublist_nil. rewrite app_nil_r. entailer!. simpl. rewrite sepcon_emp; auto.
rewrite <- Zlength_correct. lia.
(*postcon*)
entailer!. rewrite (SpaceAdjMatGraph_unfold' _ _ _ addresses 0). repeat rewrite sublist_nil. repeat rewrite iter_sepcon.iter_sepcon_nil.
rewrite sepcon_emp. rewrite sepcon_comm. rewrite sepcon_emp.
rewrite Z.add_0_l. rewrite (sublist_split 0 1 (size)). rewrite sublist_one. rewrite nat_inc_list_i.
rewrite iter_sepcon.iter_sepcon_app. rewrite Zlength_repeat. replace (Datatypes.length old_contents) with (Z.to_nat size).
rewrite <- (map_repeat (fun x => Vint (Int.repr x))).
unfold list_rep. rewrite Znth_repeat_inrange.
(*we can just simpl; entailer! here, but that relies on our size being fixed at a small number, so providing the scalable proof*)
rewrite <- (map_map Int.repr Vint).
rewrite (iter_sepcon.iter_sepcon_func_strong _
   (fun index : Z =>
         data_at Tsh (tarray tint size)
           (map Vint
              (map Int.repr
                 (Znth index
                    (repeat (repeat a (Z.to_nat size)) (Z.to_nat size)))))
           (list_address arr index))
   (fun i : Z =>
      data_at Tsh (tarray tint size) (map (fun x : Z => Vint (Int.repr x)) (repeat a (Z.to_nat size)))
              (@list_address size CompSpecs arr i))). entailer!. simpl; entailer.
intros. replace (Znth x (repeat (repeat a (Z.to_nat size)) (Z.to_nat size))) with
(repeat a (Z.to_nat size)); auto.
symmetry; apply Znth_repeat_inrange. apply sublist_In, nat_inc_list_in_iff in H3.
rewrite Z2Nat.id in H3; auto.
all: try lia.
all: try rewrite <- ZtoNat_Zlength; try lia.
rewrite Zlength_repeat; lia.
Qed.

(******************PRIM'S***************)

Lemma body_prim: semax_body Vprog Gprog f_prim prim_spec.
Proof.
start_function. rename H into Hprecon_1. rename H0 into Ha.

assert (inf_repable: repable_signed inf). {
  red. pose proof (inf_representable g). rep_lia.
}
assert (Hsz: 0 < size <= Int.max_signed). {
  apply (size_representable g).
}
assert (Hsz2: size <= Int.max_signed). {
  lia.
}
assert (size_repable: repable_signed size). {
  unfold repable_signed. rep_lia.
}

(*replace all data_at_ with data_at Vundef*)
repeat rewrite data_at__tarray.
set (k:=default_val tint); compute in k; subst k.
forward_call (v_key, (repeat Vundef (Z.to_nat size)), inf).
assert_PROP (Zlength (map (fun x : Z => Vint (Int.repr x)) garbage) = size). entailer!.
forward_call (pointer_val_val parent_ptr, (map (fun x : Z => Vint (Int.repr x)) garbage), size).
clear H garbage.
forward_call (v_out, (repeat Vundef (Z.to_nat size)), 0).
assert (Hstarting_keys: forall i, 0 <= i < size -> is_int I32 Signed (Znth i (repeat (Vint (Int.repr inf)) (Z.to_nat size)))). {
  intros. unfold is_int. rewrite Znth_repeat_inrange by lia. auto.
}
replace (repeat (Vint (Int.repr inf)) (Z.to_nat size)) with
  (map (fun x => Vint (Int.repr x)) (repeat inf (Z.to_nat size))) in *.
set (starting_keys:=map (fun x => Vint (Int.repr x)) (repeat inf (Z.to_nat size))) in *.
assert (HZlength_starting_keys: Zlength starting_keys = size). {
  unfold starting_keys. rewrite Zlength_map. rewrite Zlength_repeat; lia.
}
unfold repable_signed in inf_repable.
(*push all vertices into priq*)
forward_call(tt).
rewrite <- size_eq in *.
Intro priq_ptr.
remember (pointer_val_val priq_ptr) as v_pq.

(*push all vertices into priq*)
forward_for_simple_bound size
  (EX i : Z,
    PROP ()
    LOCAL (
      temp _pq v_pq; lvar _out (tarray tint size) v_out;
      lvar _key (tarray tint size) v_key; temp _graph (pointer_val_val gptr);
      temp _parent (pointer_val_val parent_ptr)
    )
    SEP (
      data_at Tsh (tarray tint size) (repeat (Vint (Int.repr 0)) (Z.to_nat size)) v_out;
      data_at Tsh (tarray tint size) (repeat (Vint (Int.repr size)) (Z.to_nat size)) (pointer_val_val parent_ptr);
      data_at Tsh (tarray tint size) starting_keys v_key;
      data_at Tsh (tarray tint size) (sublist 0 i starting_keys ++ sublist i size (repeat Vundef (Z.to_nat size))) v_pq;
      (@SpaceAdjMatGraph' size CompSpecs Tsh (@graph_to_symm_mat size g) (pointer_val_val gptr));
      free_tok v_pq (sizeof tint * size)
    )
  )%assert.
entailer!.
rewrite sublist_nil, sublist_same, app_nil_l.
entailer!.
trivial. rewrite Zlength_repeat; lia.

(*precon taken care of*)
(*loop*)
Transparent size.
forward.
Global Opaque size.

assert (Znth i starting_keys = Vint (Int.repr (Znth i (repeat inf (Z.to_nat size))))). {
  unfold starting_keys. rewrite Znth_map; auto.
}
forward_call (v_pq, i, Znth i (repeat inf (Z.to_nat size)), sublist 0 i starting_keys ++ sublist i size (repeat Vundef (Z.to_nat size))).
split. auto. unfold weight_inrange_priq.
rewrite Znth_repeat_inrange. lia. lia.
rewrite Znth_repeat_inrange; lia.

entailer!.
rewrite upd_Znth_app2. rewrite Zlength_sublist, Z.sub_0_r, Z.sub_diag; try lia.
rewrite (sublist_split i (i+1) size). rewrite (sublist_one i (i+1)). rewrite upd_Znth_app1.
rewrite upd_Znth0. rewrite app_assoc.
rewrite (sublist_split 0 i (i+1)). rewrite (sublist_one i (i+1)). rewrite <- H0. entailer!.
all: try lia.
rewrite Zlength_cons, Zlength_nil; lia.
rewrite Zlength_repeat. lia. lia.
rewrite Zlength_repeat; lia.
rewrite Zlength_sublist. rewrite Zlength_sublist. lia. lia. rewrite Zlength_repeat; lia. lia. lia.
rewrite sublist_nil, app_nil_r, sublist_same; try lia.
(*one last thing for convenience*)
rewrite <- (map_repeat (fun x => Vint (Int.repr x))).
rewrite <- (map_repeat (fun x => Vint (Int.repr x))).
pose proof (finGraph g) as fg.
(*whew! all setup done!*)
(*now for the pq loop*)
forward_loop (
  EX mst': G,
  EX fmst': FiniteGraph mst',
  EX parents: list V,
  EX keys: list Z, (*can give a concrete definition in SEP, but it leads to shenanigans during entailer*)
  EX pq_state: list V, (*can give a concrete definition in SEP, but it leads to shenanigans during entailer*)
  EX popped_vertices: list V,
  EX unpopped_vertices: list V,
    PROP (
      (*graph stuff*)
      is_partial_lgraph mst' g;
      uforest' mst';
      (*about the lists*)
      Permutation (popped_vertices++unpopped_vertices) (VList g);
      forall v, 0 <= v < size -> 0 <= Znth v parents <= size;
      forall v, 0 <= v < size -> Znth v keys = elabel g (eformat (v, Znth v parents));
      forall v, 0 <= v < size -> Znth v pq_state = if in_dec V_EqDec v popped_vertices then Z.add inf 1 else Znth v keys;
      forall v, 0 <= v < size -> 0 <= Znth v parents < size ->
          (evalid g (eformat (v, Znth v parents)) /\ (*together you form a valid edge in g*)
          (exists i, 0<=i<Zlength popped_vertices /\ Znth i popped_vertices = Znth v parents /\
            i < find popped_vertices v 0) /\ (*your parent has been popped, only time parents is updated, and you weren't in it when it was*)
          (forall u, In u (sublist 0 (find popped_vertices v 0) popped_vertices) -> elabel g (eformat (v, Znth v parents)) <= elabel g (eformat (u,v))) (*your current parent is the lowest among the popped, until you're popped too*) (*<-used for proving weight invar below*)
          );
      forall v, 0 <= v < size -> Znth v parents = size -> forall u, In u (sublist 0 (find popped_vertices v 0) popped_vertices) -> ~adjacent g u v;
      (*mst specific*)
      Permutation (EList mst') (map (fun v => eformat (v, Znth v parents)) (filter (fun v => Znth v parents <? size) popped_vertices));
      forall u v, In u popped_vertices -> In v popped_vertices -> (connected g u v <-> connected mst' u v);
      (*misc*)
      forall u v, In u unpopped_vertices -> ~ adjacent mst' u v;
      (*weight*)
      (* at the point of being popped, you had the lowest weight of all potential branches *)
      forall v u1 u2, In v popped_vertices -> 0 <= Znth v parents < size ->
        vvalid g u2 ->
        In u1 (sublist 0 (find popped_vertices v 0) popped_vertices) ->
        ~ In u2 (sublist 0 (find popped_vertices v 0) popped_vertices) ->
        elabel g (eformat (v, Znth v parents)) <= elabel g (eformat (u1,u2));
      (*minimality...*)
      exists M, minimum_spanning_forest M g /\ is_partial_lgraph mst' M
    )
    LOCAL (
      temp _pq v_pq; lvar _out (tarray tint size) v_out;
      temp _parent (pointer_val_val parent_ptr); lvar _key (tarray tint size) v_key;
      temp _graph (pointer_val_val gptr)
    )
    SEP (
      data_at Tsh (tarray tint size) (map (fun x => if in_dec V_EqDec x popped_vertices
        then (Vint (Int.repr 1)) else (Vint (Int.repr 0))) (nat_inc_list (Z.to_nat size))) v_out;
      data_at Tsh (tarray tint size) (map (fun x => Vint (Int.repr x)) parents) (pointer_val_val parent_ptr);
      data_at Tsh (tarray tint size) (map (fun x => Vint (Int.repr x)) keys) v_key;
      data_at Tsh (tarray tint size) (map (fun x => Vint (Int.repr x))
        pq_state) v_pq;
      (@SpaceAdjMatGraph' size CompSpecs Tsh (@graph_to_symm_mat size g) (pointer_val_val gptr));
      free_tok v_pq (sizeof tint * size)
    )
  )
break: (
  EX mst: G,
  EX fmst: FiniteGraph mst,
  EX popped_vertices: list V,
  EX parents: list V,
  EX keys: list Z,
    PROP (
      is_partial_lgraph mst g;
      uforest' mst;
      Permutation popped_vertices (VList mst);
      forall v, 0 <= v < size -> 0 <= Znth v parents < size ->
          (evalid g (eformat (v, Znth v parents)) /\ (*together you form a valid edge in g*)
          (exists i, 0<=i<Zlength popped_vertices /\ Znth i popped_vertices = Znth v parents
            /\ i < find popped_vertices v 0) /\ (*your parent has been popped, only time parents is updated, and you weren't in it when it was*)
          (forall u, In u (sublist 0 (find popped_vertices v 0) popped_vertices) -> elabel g (eformat (v, Znth v parents)) <= elabel g (eformat (u,v))) (*your current parent is the lowest among the popped, until you're popped too*) (*<-used for proving weight invar below*)
          );
      forall v, 0 <= v < size -> Znth v parents = size -> forall u, In u (sublist 0 (find popped_vertices v 0) popped_vertices) -> ~adjacent g u v;
      (*something about weight*)
      Permutation (EList mst) (map (fun v => eformat (v, Znth v parents)) (filter (fun v => Znth v parents <? size) popped_vertices));
      spanning mst g;
      (*weight*)
      forall v u1 u2, In v popped_vertices -> 0 <= Znth v parents < size ->
        vvalid g u2 ->
        In u1 (sublist 0 (find popped_vertices v 0) popped_vertices) ->
        ~ In u2 (sublist 0 (find popped_vertices v 0) popped_vertices) ->
        elabel g (eformat (v, Znth v parents)) <= elabel g (eformat (u1,u2));
      forall v, 0 <= v < size -> 0 <= Znth v parents <= size;
      (*minimality...*)
      exists M, minimum_spanning_forest M g /\ is_partial_lgraph mst M
    )
    LOCAL (
      temp _pq v_pq; lvar _out (tarray tint size) v_out;
      temp _parent (pointer_val_val parent_ptr); lvar _key (tarray tint size) v_key;
      temp _graph (pointer_val_val gptr)
    )
    SEP (
      data_at Tsh (tarray tint size) (repeat (Vint (Int.repr 1)) (Z.to_nat size)) v_out;
      data_at Tsh (tarray tint size) (map (fun x => Vint (Int.repr x)) parents) (pointer_val_val parent_ptr);
      data_at Tsh (tarray tint size) (map (fun x => Vint (Int.repr x)) keys) v_key;
      data_at Tsh (tarray tint size) (repeat (Vint (Int.repr (inf+1))) (Z.to_nat size)) v_pq;
      (@SpaceAdjMatGraph' size CompSpecs Tsh (@graph_to_symm_mat size g) (pointer_val_val gptr));
      free_tok v_pq (sizeof tint * size)
    )
  )
%assert.
(****PRECON****) {
  assert (inf_rep: 0 <= inf <= Int.max_signed). {
    pose proof (inf_representable g). rep_lia.
  }
  remember (@edgeless_graph'
            size inf
            Hsz
            (inf_representable g)) as elg.
  Exists elg.
  pose proof (finGraph elg) as fe. Exists fe.
  Exists (repeat size (Z.to_nat size)).
  Exists (repeat inf (Z.to_nat size)).
  Exists (repeat inf (Z.to_nat size)).
  Exists (nil (A:=V)).
  Exists (VList g). rewrite app_nil_l.
  assert (Hinv_1: is_partial_lgraph elg g).
  subst elg. apply edgeless_partial_lgraph.
  assert (Hinv_2: uforest' elg). subst elg. apply uforest'_edgeless_graph.
  assert (Hinv_3: Permutation (VList g) (VList g)). apply Permutation_refl; auto.
  assert (Hinv_4: forall v : Z, 0 <= v < size -> 0 <= Znth v (repeat size (Z.to_nat size)) <= size). {
    intros. rewrite Znth_repeat_inrange; lia.
  }
  assert (Hinv_5: forall v : Z, 0 <= v < size -> Znth v (repeat inf (Z.to_nat size)) =
    elabel g (eformat (v, Znth v (repeat size (Z.to_nat size))))). {
    intros.
    repeat rewrite Znth_repeat_inrange by lia. symmetry; apply (invalid_edge_weight g).
    unfold not; intros. rewrite <- (eformat_adj g) in H0. apply adjacent_requires_vvalid in H0. destruct H0.
    rewrite vert_bound in H1. lia.
  }
  assert (Hinv_6: forall v : Z,
    0 <= v < size ->
    Znth v (repeat inf (Z.to_nat size)) =
    (if in_dec V_EqDec v (nil (A:=V))
     then (inf + 1)%Z
     else Znth v (repeat inf (Z.to_nat size)))). {
    intros. destruct (in_dec V_EqDec v []); [contradiction | auto].
  }
  assert (Hinv_7: forall v : Z, 0 <= v < size ->
    0 <= Znth v (repeat size (Z.to_nat size)) < size ->
    evalid g (eformat (v, Znth v (repeat size (Z.to_nat size)))) /\
    (exists i : Z, 0 <= i < Zlength (nil (A:=V)) /\
       Znth i (nil (A:=V)) = Znth v (repeat size (Z.to_nat size)) /\ i < find (nil (A:=V)) v 0) /\
    (forall u : V,
     In u (sublist 0 (find (nil (A:=V)) v 0) (nil (A:=V))) ->
     elabel g (eformat (v, Znth v (repeat size (Z.to_nat size)))) <=
     elabel g (eformat (u, v)))). {
    intros. rewrite Znth_repeat_inrange in H0; lia. }
  assert (Hinv_8: forall v : Z, 0 <= v < size ->
    Znth v (repeat size (Z.to_nat size) ) = size ->
    forall u : V, In u (sublist 0 (find [] v 0) []) -> ~ adjacent g u v). {
    intros. rewrite sublist_nil in H1. contradiction. }
  assert (Hinv_9: Permutation (EList elg)
      (map (fun v : Z => eformat (v, Znth v (repeat size (Z.to_nat size))))
         (filter (fun v : Z => Znth v (repeat size (Z.to_nat size)) <? size) []))). {
    simpl.
    (*because I've trouble using edgeless_graph_EList*) apply NoDup_Permutation. apply NoDup_EList. apply NoDup_nil.
    intros. rewrite EList_evalid. split; intros.
    subst elg.
    pose proof (@edgeless_graph_evalid size inf (inf_representable g) Hsz x); contradiction. contradiction.
  }
  (*Hinv_12 (nil <> nil) seems to be missing, autoresolved?*)
  assert (Hinv_11: forall u v : V, In u (VList g) -> ~ adjacent elg u v). {
    unfold not; intros. destruct H0 as [e [? ?]]. destruct H0.
    subst elg.
    pose proof (@edgeless_graph_evalid size inf (inf_representable g) Hsz e); contradiction.
  }
  assert (Hinv_12: forall v u1 u2 : V,
    In v (nil (A:=V)) ->
    0 <= Znth v (repeat size (Z.to_nat size)) < size ->
    vvalid g u2 ->
    In u1 (sublist 0 (find (nil (A:=V)) v 0) (nil (A:=V))) ->
    ~ In u2 (sublist 0 (find (nil (A:=V)) v 0) (nil (A:=V))) ->
    elabel g (eformat (v, Znth v (repeat size (Z.to_nat size)))) <=
    elabel g (eformat (u1, u2))). {
    intros. contradiction.
  }
  assert (Hinv_13: exists M, minimum_spanning_forest M g /\ is_partial_lgraph elg M). {
    destruct (exists_msf g) as [M ?]. exists M; split. auto.
    subst elg. apply edgeless_partial_lgraph.
  }

  (*fix up the SEP*)
  replace (map (fun x : V => if in_dec V_EqDec x [] then Vint (Int.repr 1) else Vint (Int.repr 0)) (nat_inc_list (Z.to_nat size)))
    with (map (fun x : Z => Vint (Int.repr x)) (repeat 0 (Z.to_nat size))). 2: {
    apply list_eq_Znth. repeat rewrite Zlength_map. rewrite Zlength_repeat by lia. rewrite nat_inc_list_Zlength, Z2Nat.id; lia.
    intros. rewrite Zlength_map, Zlength_repeat in H by lia.
    rewrite Znth_map. 2: rewrite Zlength_repeat; lia.
    rewrite Znth_repeat_inrange by lia.
    rewrite Znth_map. 2: rewrite nat_inc_list_Zlength, Z2Nat.id; lia.
    rewrite nat_inc_list_i. 2: rewrite Z2Nat.id; lia.
    destruct (in_dec V_EqDec i []); [contradiction | auto].
  }
  unfold starting_keys.
  time "main loop precon:" entailer!.
}
(****MAIN LOOP****) {
  clear Hstarting_keys HZlength_starting_keys starting_keys.
  Intros mst' fmst' parents keys pq_state popped_vertices unpopped_vertices.
  (*do a mass renaming for convenience*)
  rename H into Hinv_1; rename H0 into Hinv_2;
  rename H1 into Hinv_3; rename H2 into Hinv_4;
  rename H3 into Hinv_5; rename H4 into Hinv_6;
  rename H5 into Hinv_7; rename H6 into Hinv_8;
  rename H7 into Hinv_9; rename H8 into Hinv_10;
  rename H9 into Hinv_11; rename H10 into Hinv_12;
  rename H11 into Hinv_13.
  (*15 invariants... I think, that if we go with this "exists M" approach, we can eliminate some of the weight lemmas*)
  assert_PROP (Zlength (map (fun x : Z => Vint (Int.repr x)) parents) = size /\
              Zlength (map (fun x : Z => Vint (Int.repr x)) keys) = size /\
              Zlength (map (fun x : Z => Vint (Int.repr x)) pq_state) = size
  ). entailer!.
  repeat rewrite Zlength_map in H. destruct H as [HZlength_parents [HZlength_keys HZlength_pq_state]].
  assert (Hpopped_or_unpopped: forall v, vvalid g v -> In v popped_vertices \/ In v unpopped_vertices). {
    intros. apply in_app_or. apply (Permutation_in (l:=VList g)). apply Permutation_sym; auto. apply VList_vvalid; auto.
  }
  (*^^significant lag from the three entailers above*)
  assert (Hpopped_vvalid: forall v, In v popped_vertices -> vvalid g v). {
    intros. rewrite <- VList_vvalid. apply (Permutation_in (l:=popped_vertices++unpopped_vertices)).
    apply Hinv_3. apply in_or_app; left; auto.
  }
  assert (Hunpopped_vvalid: forall v, In v unpopped_vertices -> vvalid g v). {
    intros. rewrite <- VList_vvalid. apply (Permutation_in (l:=popped_vertices++unpopped_vertices)).
    apply Hinv_3. apply in_or_app; right; auto.
  }
  assert (@inrange_priq inf pq_state). {
    unfold inrange_priq. rewrite Forall_forall. intros x Hx.
    rewrite In_Znth_iff in Hx. destruct Hx as [i [? ?]]. rewrite HZlength_pq_state in H. subst x.
    rewrite Hinv_6. 2: lia. destruct (in_dec V_EqDec i popped_vertices). lia.
    rewrite Hinv_5. 2: lia.
    split. apply weight_representable. apply (Z.le_trans _ inf). apply weight_inf_bound. lia.
  }
  replace (data_at Tsh (tarray tint size) (map (fun x : Z => Vint (Int.repr x)) pq_state) v_pq)
    with (data_at Tsh (tarray tint size) (map Vint (map Int.repr pq_state)) v_pq).
  2: { rewrite list_map_compose. auto. }
  forward_call (v_pq, pq_state).
  forward_if.
  (*PROCEED WITH LOOP*) {
  assert (@isEmpty inf pq_state = Vzero). {
    destruct (@isEmptyTwoCases inf pq_state);
    rewrite H1 in H0; simpl in H0; now inversion H0.
  }
  forward_call (v_pq, pq_state).
  Intros u. rename H2 into Hu.
  assert (0 <= u < size). {
    rewrite Hu. rewrite <- HZlength_pq_state. apply find_range.
    apply min_in_list. apply incl_refl. destruct pq_state.
    rewrite Zlength_nil in HZlength_pq_state. lia. 
    simpl. left; trivial.
  }
  assert (Hu_not_popped: ~ In u popped_vertices). { unfold not; intros.
    assert (Znth u pq_state < inf + 1). apply (find_min_lt_inf u pq_state Hu H1).
    rewrite HZlength_pq_state; lia. rewrite Hinv_6 in H4 by lia.
    destruct (in_dec V_EqDec u popped_vertices). lia. contradiction.
  }
  assert (Hu_unpopped: In u unpopped_vertices). { destruct (Hpopped_or_unpopped u).
    rewrite (vvalid_meaning g). auto. contradiction. auto.
  }
  forward.
  replace (upd_Znth u (map (fun x : V =>
    if in_dec V_EqDec x popped_vertices then Vint (Int.repr 1) else Vint (Int.repr 0))
    (nat_inc_list (Z.to_nat size))) (Vint (Int.repr 1))) with (map (fun x : V =>
    if in_dec V_EqDec x (popped_vertices+::u) then Vint (Int.repr 1) else Vint (Int.repr 0))
    (nat_inc_list (Z.to_nat size))).
  2: { apply list_eq_Znth. rewrite Zlength_upd_Znth. do 2 rewrite Zlength_map. auto.
    intros. rewrite Zlength_map in H3. rewrite nat_inc_list_Zlength in H3.
    destruct (Z.eq_dec i u). subst i.
    +rewrite upd_Znth_same. rewrite Znth_map.
    rewrite nat_inc_list_i. assert (In u (popped_vertices+::u)). apply in_or_app. right; simpl; auto.
    destruct (in_dec V_EqDec u (popped_vertices+::u)). auto. contradiction.
    lia. rewrite nat_inc_list_Zlength; lia.
    rewrite Zlength_map, nat_inc_list_Zlength; lia.
    +rewrite upd_Znth_diff. rewrite Znth_map. rewrite Znth_map. rewrite nat_inc_list_i.
    destruct (in_dec V_EqDec i (popped_vertices+::u));
    destruct (in_dec V_EqDec i popped_vertices). auto.
    apply in_app_or in i0; destruct i0. contradiction. destruct H4. symmetry in H4; contradiction. contradiction.
    assert (In i (popped_vertices+::u)). apply in_or_app. left; auto. contradiction.
    auto. auto. rewrite nat_inc_list_Zlength; auto. rewrite nat_inc_list_Zlength; auto.
    rewrite Zlength_map, nat_inc_list_Zlength; auto.
    rewrite Zlength_map, nat_inc_list_Zlength; auto.
    auto.
  }
  rewrite upd_Znth_map. rewrite upd_Znth_map. rewrite list_map_compose. (*pq state*)
  replace (Znth 0 pq_state) with (hd 0 pq_state). rewrite <- Hu. 2: { destruct pq_state. rewrite Zlength_nil in HZlength_pq_state; lia. simpl. rewrite Znth_0_cons. auto. }
  assert (Hu_min: forall v, 0 <= v < size -> Znth u pq_state <= Znth v pq_state). {
    intros. rewrite Hu. rewrite Znth_find.
    apply fold_min. apply Znth_In. lia.
    apply fold_min_in_list. lia.
  }
  clear Hu. set (upd_pq_state:=upd_Znth u pq_state (inf + 1)).
  (*for loop to update un-popped vertices' min weight.
  The result is every vertex who's NOT in popped_vertices and connected, as their weight maintained or lowered*)
  forward_for_simple_bound size (
    EX i: Z,
    EX parents': list Z,
    EX keys': list Z,
    EX pq_state': list Z,
      PROP (
        (*if you were already popped (out=1) or not adjacent, nothing happens*)
        forall v, 0<=v<i -> (~adjacent g u v \/ In v (popped_vertices+::u)) -> (
          Znth v parents' = Znth v parents /\
          Znth v keys' = Znth v keys /\
          Znth v pq_state' = Znth v upd_pq_state);
        (*if you are still in pq and adjacent, you are updated*)
        forall v, 0<=v<i -> adjacent g u v -> ~ In v (popped_vertices+::u) -> (
          Znth v parents' = (if Z.ltb (elabel g (eformat (u,v))) (Znth v upd_pq_state) then u else Znth v parents) /\
          Znth v keys' = Z.min (elabel g (eformat (u,v))) (Znth v upd_pq_state) /\
          Znth v pq_state' = Z.min (elabel g (eformat (u,v))) (Znth v upd_pq_state));
        (*no change for those that haven't been checked*)
        forall v, i<=v<size -> (
          Znth v parents' = Znth v parents /\
          Znth v keys' = Znth v keys /\
          Znth v pq_state' = Znth v upd_pq_state
        );
        forall v, 0 <= v < size -> Int.min_signed <= Znth v keys' <= inf
        (*for convenience, unpopped and not u -> Znth v keys = Znth v pq_state'?*)
      )
      LOCAL (
        temp _u (Vint (Int.repr u)); temp _t'2 (@isEmpty inf pq_state); temp _pq v_pq; lvar _out (tarray tint size) v_out;
        temp _parent (pointer_val_val parent_ptr); lvar _key (tarray tint size) v_key; temp _graph (pointer_val_val gptr)
      )
      SEP (data_at Tsh (tarray tint size) (map (fun x => Vint (Int.repr x)) pq_state') v_pq;
     data_at Tsh (tarray tint size)
       (map
          (fun x : V =>
           if in_dec V_EqDec x (popped_vertices+::u) then Vint (Int.repr 1) else Vint (Int.repr 0))
          (nat_inc_list (Z.to_nat size))) v_out;
     data_at Tsh (tarray tint size) (map (fun x : Z => Vint (Int.repr x)) parents') (pointer_val_val parent_ptr);
     data_at Tsh (tarray tint size) (map (fun x : Z => Vint (Int.repr x)) keys') v_key;
     (@SpaceAdjMatGraph' size CompSpecs Tsh (@graph_to_symm_mat size g) (pointer_val_val gptr));
      free_tok v_pq (sizeof tint * size)
      )
    )
  %assert.
  (*precon*) {
    Exists parents. Exists keys. Exists upd_pq_state. entailer!.
    (*in this case, proving the PROPs beforehand did not improve the timing*)
    intros. rewrite Hinv_5 by lia. split.
    apply weight_representable. apply weight_inf_bound.
  }
  (*loop*)
  assert (is_int I32 Signed (if in_dec V_EqDec (Znth i (nat_inc_list (Z.to_nat size))) (popped_vertices+::u)
    then Vint (Int.repr 1) else Vint (Int.repr 0))). {
    unfold is_int. rewrite nat_inc_list_i. 2: rewrite Z2Nat.id; lia.
    destruct (in_dec V_EqDec i (popped_vertices+::u)); auto.
  } forward.
  rename H5 into Hinv2_1; rename H6 into Hinv2_2;
  rename H7 into Hinv2_3; rename H8 into Hinv2_4.
  assert_PROP (Zlength (map (fun x : Z => Vint (Int.repr x)) parents') = size /\
                Zlength (map (fun x : Z => Vint (Int.repr x)) keys') = size /\
                Zlength (map (fun x : Z => Vint (Int.repr x)) pq_state') = size). entailer!.
  repeat rewrite Zlength_map in H5. destruct H5 as [? [? ?]].
  rename H5 into HZlength_parents'. rename H6 into HZlength_keys'. rename H7 into HZlength_pq_state'.
  rewrite nat_inc_list_i. 2: rewrite Z2Nat.id; lia.
  set (out_i:=if in_dec V_EqDec i (popped_vertices+::u)
               then Vint (Int.repr 1)
               else Vint (Int.repr 0)). fold out_i.
  forward_if.
  (**In queue**)
  +assert (~ In i (popped_vertices+::u)). {
    destruct (in_dec V_EqDec i (popped_vertices +:: u)). simpl in H5. inversion H5. auto.
  }
   Transparent size.
   forward_call (g, gptr, addresses, u, i).
   Global Opaque size.
   forward.
   forward_if.
    -(*g[u][i] < ...*)
      (*implies adjacency*)
    rewrite graph_to_mat_eq in H7; try lia. rewrite eformat_symm in H7.
    rewrite Int.signed_repr in H7. rewrite Int.signed_repr in H7.
    2: { assert (Int.min_signed <= Znth i keys' <= inf). apply Hinv2_4; lia.
      set (k:=Int.max_signed); compute in k; subst k. rewrite inf_eq in H8; lia. }
    2: { apply weight_representable. }
    assert (Hadj_ui: adjacent g u i). {
      rewrite eformat_adj_elabel.
      assert (Znth i keys' <= inf). apply Hinv2_4. lia.
      apply (Z.lt_le_trans _ (Znth i keys')); auto.
    }
    forward. forward. forward. entailer!.
    rewrite upd_Znth_same. simpl. auto. rewrite Zlength_map. rewrite HZlength_keys'. auto.
    rewrite upd_Znth_same. 2: { simpl. auto. rewrite Zlength_map. rewrite HZlength_keys'. auto. }
    forward_call (v_pq, i, Znth i (Znth u (@graph_to_symm_mat size g)), pq_state').
    replace (map (fun x : Z => Vint (Int.repr x)) pq_state') with (map Vint (map Int.repr pq_state')).
    entailer!. rewrite list_map_compose. auto.
    unfold weight_inrange_priq.
    rewrite graph_to_mat_eq. split.
    apply weight_representable. rewrite eformat_adj_elabel, eformat_symm in Hadj_ui.
    fold V in *. lia. lia. lia.
    Exists (upd_Znth i parents' u).
    Exists (upd_Znth i keys' (Znth i (Znth u (@graph_to_symm_mat size g)))).
    Exists (upd_Znth i pq_state' (Znth i (Znth u (@graph_to_symm_mat size g)))).
    rewrite (@SpaceAdjMatGraph_unfold' _ _ _ _ _ addresses u). unfold list_rep.
    rewrite list_map_compose. repeat rewrite (upd_Znth_map (fun x => Vint (Int.repr x))).
    2: lia. 
    clear H0 H5.
    assert (Hx1: forall v : Z, 0 <= v < i + 1 ->
      ~ adjacent g u v \/ In v (popped_vertices +:: u) ->
      Znth v (upd_Znth i parents' u) = Znth v parents /\
      Znth v (upd_Znth i keys' (Znth i (Znth u (@graph_to_symm_mat size g)))) = Znth v keys /\
      Znth v (upd_Znth i pq_state' (Znth i (Znth u (@graph_to_symm_mat size g)))) =
      Znth v upd_pq_state). {
      intros. destruct (Z.lt_trichotomy v i). repeat rewrite upd_Znth_diff; try lia. apply Hinv2_1. lia. apply H5.
      destruct H8. subst v. destruct H5; contradiction. lia.
    }
    assert (Hx2: forall v : Z,
    0 <= v < i + 1 ->
    adjacent g u v ->
    ~ In v (popped_vertices +:: u) ->
    Znth v (upd_Znth i parents' u) =
    (if elabel g (eformat (u, v)) <? Znth v upd_pq_state then u else Znth v parents) /\
    Znth v (upd_Znth i keys' (Znth i (Znth u (@graph_to_symm_mat size g)))) =
    Z.min (elabel g (eformat (u, v))) (Znth v upd_pq_state) /\
    Znth v (upd_Znth i pq_state' (Znth i (Znth u (@graph_to_symm_mat size g)))) =
    Z.min (elabel g (eformat (u, v))) (Znth v upd_pq_state)). {
      intros. destruct (Z.lt_trichotomy v i).
        (*v<i*) repeat rewrite upd_Znth_diff; try lia. apply Hinv2_2. lia. auto. auto.
        destruct H9.
        (*v=i*) subst v. repeat rewrite upd_Znth_same; try lia.
        (*i not in popped, so must be in unpopped, which means upd_pq_state = pq_state = keys*)
        assert (Znth i upd_pq_state = Znth i keys').
          unfold upd_pq_state. rewrite upd_Znth_diff. 2: replace (Zlength pq_state) with size; lia. 2: replace (Zlength pq_state) with size; lia.
          replace (Znth i keys') with (Znth i keys). rewrite Hinv_6.
          destruct (in_dec V_EqDec i popped_vertices). exfalso; apply H8. apply in_or_app; left; auto. auto. lia.
          symmetry. apply Hinv2_3. lia. unfold not; intros. apply H8. apply in_or_app; right; subst i; left; auto.
        rewrite H9. split3.
        rewrite <- (@graph_to_mat_eq size); try lia. destruct (Znth u (Znth i (@graph_to_symm_mat size g)) <? Znth i keys') eqn:bool.
        auto. rewrite graph_to_mat_eq in bool; try lia. rewrite Z.ltb_nlt in bool. contradiction.
        rewrite graph_to_mat_eq; try lia. rewrite eformat_symm. rewrite Zlt_Zmin; auto.
        rewrite graph_to_mat_eq; try lia. rewrite eformat_symm. rewrite Zlt_Zmin; auto.
        (*v>i*) lia.
    } (*60s to 33s*)
    assert(Hx3: forall v : Z,
    i + 1 <= v < size ->
    Znth v (upd_Znth i parents' u) = Znth v parents /\
    Znth v (upd_Znth i keys' (Znth i (Znth u (@graph_to_symm_mat size g)))) = Znth v keys /\
    Znth v (upd_Znth i pq_state' (Znth i (Znth u (@graph_to_symm_mat size g)))) = Znth v upd_pq_state). {
      intros. repeat rewrite upd_Znth_diff; try lia. apply Hinv2_3. lia.
    } (*entailer unable to solve but no change to timing*)
    assert (Hx4: forall v : Z,
    0 <= v < size ->
    Int.min_signed <= Znth v (upd_Znth i keys' (Znth i (Znth u (@graph_to_symm_mat size g)))) <= inf). {
      intros. destruct (Z.eq_dec v i). subst i. rewrite upd_Znth_same. rewrite graph_to_mat_eq.
      split. apply (weight_representable g (eformat (v,u))). apply weight_inf_bound. lia. lia. rewrite HZlength_keys'; lia.
      rewrite upd_Znth_diff. apply Hinv2_4. auto. rewrite HZlength_keys'; lia.
      rewrite HZlength_keys'; lia. auto.
    } (*entailer unable to solve but no change to timing*)
    time "inner loop update-because-lt-postcon (orig 71 seconds)" entailer!.
    unfold graph_to_symm_mat. rewrite graph_to_mat_Zlength; lia.
    -forward. (*nothing changed*)
    Exists parents'. Exists keys'. Exists pq_state'.
    rewrite (@SpaceAdjMatGraph_unfold' _ _ _ _ _ addresses u). unfold list_rep.
    2: lia.
    2: unfold graph_to_symm_mat; rewrite graph_to_mat_Zlength; lia.
    assert (Hx1: forall v : Z,
          0 <= v < i + 1 ->
          ~ adjacent g u v \/ In v (popped_vertices +:: u) ->
          Znth v parents' = Znth v parents /\
          Znth v keys' = Znth v keys /\ Znth v pq_state' = Znth v upd_pq_state). {
      intros. destruct (Z.lt_trichotomy v i). apply Hinv2_1; auto. lia. destruct H10.
      subst v. apply Hinv2_3. lia. lia.
    } (*60s to 53s*)
    assert (Hx2: forall v : Z,
      0 <= v < i + 1 ->
      adjacent g u v ->
      ~ In v (popped_vertices +:: u) ->
      Znth v parents' =
      (if elabel g (eformat (u, v)) <? Znth v upd_pq_state then u else Znth v parents) /\
      Znth v keys' = Z.min (elabel g (eformat (u, v))) (Znth v upd_pq_state) /\
      Znth v pq_state' = Z.min (elabel g (eformat (u, v))) (Znth v upd_pq_state)). {
      intros. destruct (Z.lt_trichotomy v i).
      (*v < i*) apply Hinv2_2. lia. auto. auto.
      destruct H11.
      (*v = i*) subst v. rewrite <- (@graph_to_mat_eq size); try lia.
      assert (Znth i upd_pq_state = Znth i keys'). {
        unfold upd_pq_state. rewrite upd_Znth_diff. 2: replace (Zlength pq_state) with size; lia.  2: replace (Zlength pq_state) with size; lia.
        replace (Znth i keys') with (Znth i keys). rewrite Hinv_6.
        destruct (in_dec V_EqDec i popped_vertices). exfalso. apply H10. apply in_or_app; left; auto.
        auto. lia. symmetry. apply Hinv2_3. lia. unfold not; intros. apply H10. apply in_or_app; right; subst i; left; auto.
      } rewrite H11. rewrite graph_to_mat_symmetric; try lia.
      rewrite !Int.signed_repr in H7. split3.
      destruct (Znth i (Znth u (@graph_to_symm_mat size g)) <? Znth i keys') eqn:bool.
      rewrite Z.ltb_lt in bool. lia.
      apply Hinv2_3. lia.
      rewrite Z.min_r; lia.
      replace (Znth i pq_state') with (Znth i upd_pq_state). rewrite H11. rewrite Z.min_r; lia. symmetry; apply Hinv2_3; lia.
      assert (Int.min_signed <= Znth i keys' <= inf). apply Hinv2_4. lia. pose proof (inf_repable); unfold repable_signed in H13; lia.
      rewrite graph_to_mat_eq; try lia. apply weight_representable.
      (*v > i*) lia.
    } (*53s to 30s*)
    assert (Hx3: forall v : Z,
      i + 1 <= v < size ->
      Znth v parents' = Znth v parents /\
      Znth v keys' = Znth v keys /\ Znth v pq_state' = Znth v upd_pq_state). {
      intros. apply Hinv2_3. lia.
    } (*entailer unable to solve but no change to timing*)
    time "inner loop no-update-because-not-lt-postcon (originally 60s)" entailer!.
  +(*nothing changed because out of pq*)
  assert (In i (popped_vertices+::u)). {
    unfold typed_false in H5. destruct (V_EqDec u i); simpl in H5. unfold Equivalence.equiv in e; subst i. apply in_or_app; right; left; auto.
    destruct (in_dec V_EqDec i (popped_vertices+::u)); simpl in H5. auto. inversion H5.
  }
  forward. (*again nothing changed*)
  Exists parents'. Exists keys'. Exists pq_state'.
  rewrite (@SpaceAdjMatGraph_unfold' _ _ _ _ _ addresses u). unfold list_rep.
  2: lia.
  2: unfold graph_to_symm_mat; rewrite graph_to_mat_Zlength; lia. 
  assert (forall v : Z,
          0 <= v < i + 1 ->
          ~ adjacent g u v \/ In v (popped_vertices +:: u) ->
          Znth v parents' = Znth v parents /\
          Znth v keys' = Znth v keys /\ Znth v pq_state' = Znth v upd_pq_state). {
    intros. destruct (Z.lt_trichotomy v i). apply Hinv2_1; auto. lia. destruct H9. subst v. apply Hinv2_3. lia. lia.
  }
  assert (forall v : Z,
    0 <= v < i + 1 ->
    adjacent g u v ->
    ~ In v (popped_vertices +:: u) ->
    Znth v parents' =
    (if elabel g (eformat (u, v)) <? Znth v upd_pq_state then u else Znth v parents) /\
    Znth v keys' = Z.min (elabel g (eformat (u, v))) (Znth v upd_pq_state) /\
    Znth v pq_state' = Z.min (elabel g (eformat (u, v))) (Znth v upd_pq_state)). {
    intros. destruct (Z.lt_trichotomy v i). apply Hinv2_2. lia. auto. auto.
    destruct H11. subst v. contradiction. (*i is popped*) lia.
  }
  assert (forall v : Z,
    i + 1 <= v < size ->
    Znth v parents' = Znth v parents /\
    Znth v keys' = Znth v keys /\ Znth v pq_state' = Znth v upd_pq_state). {
    intros. apply Hinv2_3. lia.
  }
  time "inner loop no-update-because-out-postcon (originally 92 seconds):" entailer!.
  +(*inner loop done, postcon leading to next outer loop iter*)
  Intros parents' keys' pq_state'.
  assert (Htmp: Znth u parents' = Znth u parents /\ Znth u keys' = Znth u keys /\ Znth u pq_state' = Znth u upd_pq_state). {
    apply H3. lia. right; apply in_or_app; right; left; auto.
  } destruct Htmp as [Hu_parents [Hu_keys Hu_pq_state]].
  (*need to split into two cases: if Znth u keys = inf, then it's a "starter" and so the same mst. Else, it's adde(eformat (u, Znth u keys))*)
  clear H5. rename H3 into Hinv2_1; rename H4 into Hinv2_2; rename H6 into Hinv2_3.
  assert (0 <= Znth u parents). { apply Hinv_4. auto. }
  assert (Znth u parents <= size). { apply Hinv_4. auto. }
  (*****We do as many props as we can here, especially the non-mst ones*****)
  assert (Hperm_g: Permutation (popped_vertices +:: u ++ remove V_EqDec u unpopped_vertices) (VList g)). {
    assert (NoDup unpopped_vertices). apply (NoDup_app_r V popped_vertices). apply (Permutation_NoDup (l:=VList g)). apply Permutation_sym; auto.
    apply NoDup_VList.
    rewrite <- app_assoc. simpl. apply (Permutation_trans (l':=popped_vertices++unpopped_vertices)).
    apply Permutation_app_head. apply NoDup_Permutation. apply NoDup_cons. apply remove_In.
    apply nodup_remove_nodup. auto. auto. intros; split; intros.
    destruct H6. subst x. auto. rewrite remove_In_iff in H6. apply H6.
    destruct (V_EqDec x u). unfold Equivalence.equiv in e. subst x. left; auto.
    unfold RelationClasses.complement, Equivalence.equiv in c. right. rewrite remove_In_iff. split; auto.
    auto.
  }
  assert (Hparents_bound: forall v : Z, 0 <= v < size -> 0 <= Znth v parents' <= size). {
    intros. destruct (adjacent_dec g u v). destruct (in_dec Z.eq_dec v (popped_vertices +::u)).
    replace (Znth v parents') with (Znth v parents). 2: symmetry; apply Hinv2_1; auto. apply Hinv_4; auto.
    replace (Znth v parents') with (if elabel g (eformat (u, v)) <? Znth v upd_pq_state then u else Znth v parents).
    2: symmetry; apply (Hinv2_2 v); auto. rewrite <- (@graph_to_mat_eq size); auto.
    destruct (Znth u (Znth v (@graph_to_symm_mat size g)) <? Znth v upd_pq_state) eqn:bool. lia. apply Hinv_4; auto.
    replace (Znth v parents') with (Znth v parents). 2: symmetry; apply Hinv2_1; auto. apply Hinv_4; auto.
  }
  assert (Hkeys': forall v : Z, 0 <= v < size -> Znth v keys' = elabel g (eformat (v, Znth v parents'))). {
    intros. destruct (adjacent_dec g u v). destruct (in_dec Z.eq_dec v (popped_vertices +::u)).
    ****
    replace (Znth v keys') with (Znth v keys). 2: symmetry; apply Hinv2_1; auto. rewrite Hinv_5.
    replace (Znth v parents') with (Znth v parents). 2: symmetry; apply Hinv2_1; auto. auto. auto.
    ****
    replace (Znth v keys') with (Z.min (elabel g (eformat (u, v))) (Znth v upd_pq_state)). 2: symmetry; apply Hinv2_2; auto.
    replace (Znth v parents') with (if elabel g (eformat (u, v)) <? Znth v upd_pq_state then u else Znth v parents). 2: symmetry; apply Hinv2_2; auto.
    rewrite <- (@graph_to_mat_eq size) by lia. destruct (Znth u (Znth v (@graph_to_symm_mat size g)) <? Znth v upd_pq_state) eqn:bool.
    rewrite graph_to_mat_eq by lia. rewrite graph_to_mat_eq in bool by lia. rewrite Z.ltb_lt in bool. rewrite Zlt_Zmin by auto. rewrite eformat_symm; auto.
    rewrite graph_to_mat_eq by lia. rewrite graph_to_mat_eq in bool by lia. rewrite Z.ltb_ge in bool. rewrite Z.min_r by auto.
    unfold upd_pq_state. destruct (Z.eq_dec v u). subst v. exfalso; apply n. apply in_or_app; right; left; auto.
    rewrite upd_Znth_diff. rewrite Hinv_6 by lia. destruct (in_dec V_EqDec v popped_vertices). exfalso; apply n. apply in_or_app; left; auto.
    rewrite Hinv_5 by lia. auto.
    replace (Zlength pq_state) with size by lia. lia.
    replace (Zlength pq_state) with size by lia. lia. auto.
    ****
    replace (Znth v keys') with (Znth v keys). 2: symmetry; apply Hinv2_1; auto. rewrite Hinv_5.
    replace (Znth v parents') with (Znth v parents). 2: symmetry; apply Hinv2_1; auto. auto. auto.
  }
  assert (Hpq_state': forall v : Z, 0 <= v < size -> Znth v pq_state' = (if in_dec V_EqDec v (popped_vertices +:: u) then inf + 1 else Znth v keys')). {
    intros. destruct (in_dec V_EqDec v (popped_vertices +:: u)).
    replace (Znth v pq_state') with (Znth v upd_pq_state). 2: symmetry; apply Hinv2_1; auto. unfold upd_pq_state.
    apply in_app_or in i; destruct i.
    rewrite upd_Znth_diff. rewrite Hinv_6 by lia. destruct (in_dec V_EqDec v popped_vertices). auto. contradiction.
    replace (Zlength pq_state) with size; lia. replace (Zlength pq_state) with size; lia.
    unfold not; intros; subst v. contradiction.
    destruct H6. subst v. rewrite upd_Znth_same. auto. replace (Zlength pq_state) with size; lia.
    contradiction.
    destruct (adjacent_dec g u v).
    (*second case*)
    replace (Znth v pq_state') with (Z.min (elabel g (eformat (u, v))) (Znth v upd_pq_state)). 2: symmetry; apply Hinv2_2; auto.
    replace (Znth v keys') with (Z.min (elabel g (eformat (u, v))) (Znth v upd_pq_state)). 2: symmetry; apply Hinv2_2; auto.
    auto.
    (*third case*)
    replace (Znth v pq_state') with (Znth v upd_pq_state). 2: symmetry; apply Hinv2_1; auto. unfold upd_pq_state.
    rewrite upd_Znth_diff. rewrite Hinv_6 by lia. destruct (in_dec V_EqDec v popped_vertices).
    exfalso; apply n. apply in_or_app; left; auto.
    symmetry; apply Hinv2_1; auto. unfold upd_pq_state.
    replace (Zlength pq_state) with size; lia. replace (Zlength pq_state) with size; lia.
    unfold not; intros. subst v. apply n. apply in_or_app; right; left; auto.
  }
  assert (Hheavy: forall v : Z, 0 <= v < size -> 0 <= Znth v parents' < size ->
    evalid g (eformat (v, Znth v parents')) /\
    (exists i : Z, 0 <= i < Zlength (popped_vertices +:: u) /\
      Znth i (popped_vertices +:: u) = Znth v parents' /\
      i < find (popped_vertices+::u) v 0)
    /\ (forall u0 : V,
     In u0 (sublist 0 (find (popped_vertices +:: u) v 0) (popped_vertices +:: u)) ->
     elabel g (eformat (v, Znth v parents')) <= elabel g (eformat (u0, v)))). {
    intros. (*the main issue is u and unpopped; popped_vertices is an application of Hinv2_1 and Hinv_7*)
    destruct (in_dec V_EqDec v (popped_vertices+::u)).
    (*v in popped_vertices+::u*)
    replace (Znth v parents') with (Znth v parents). 2: symmetry; apply Hinv2_1; auto.
    replace (Znth v parents') with (Znth v parents) in H6. 2: symmetry; apply Hinv2_1; auto.
    destruct (Hinv_7 v H5 H6). destruct H8 as [[j [? ?]] ?].
    split. auto. split. exists j. split.
    rewrite Zlength_app. rewrite Zlength_cons, Zlength_nil. lia.
    split. rewrite app_Znth1 by lia. apply H9.
    destruct H9. apply (Z.lt_le_trans _ (find popped_vertices v 0)). auto. apply find_app_le.
    intros.
    apply H10. rewrite sublist_app1 in H11. auto.
    2: { split. lia. apply (find_range_gen (popped_vertices+::u) v 0). auto. lia. }
    2: { assert (0 <= find (popped_vertices +:: u) v 0 < Zlength (popped_vertices +:: u)).
        apply (find_range (popped_vertices+::u) v). auto. rewrite Zlength_app, Zlength_cons, Zlength_nil in H12. lia. }
    destruct (V_EqDec v u).
    (*subcase v = u*) hnf in e. subst v.
    replace (find (popped_vertices +:: u) u 0) with (Zlength popped_vertices) in H11.
    replace (find popped_vertices u 0) with (Zlength popped_vertices). auto.
    rewrite find_notIn_0; auto.
    rewrite find_app_notIn1. rewrite find_cons. rewrite Z.add_0_r. auto. auto.
    (*subcase v <> u*) unfold RelationClasses.complement, Equivalence.equiv in c.
    assert (In v popped_vertices). apply in_app_or in i; destruct i. auto. destruct H12. symmetry in H12; contradiction. contradiction.
    replace (find (popped_vertices +:: u) v 0) with (find popped_vertices v 0) in H11. auto.
    symmetry; apply find_app_In1. auto.
    (*****NOT IN POPPED_VERTICES+::U*****)
    assert (In v (remove V_EqDec u unpopped_vertices)). destruct (Hpopped_or_unpopped v). rewrite vert_bound; auto.
    exfalso; apply n; apply in_or_app; left; auto. rewrite remove_In_iff. split. auto. unfold not; intros.
    subst v. apply n; apply in_or_app; right; left; auto.
    destruct (adjacent_dec g u v).
    (*adjacent*)
    replace (Znth v parents') with (if elabel g (eformat (u, v)) <? Znth v upd_pq_state then u else Znth v parents).
    2: symmetry; apply Hinv2_2; auto.
    replace (Znth v parents') with (if elabel g (eformat (u, v)) <? Znth v upd_pq_state then u else Znth v parents) in H6.
    2: symmetry; apply Hinv2_2; auto.
    rewrite <- ((@graph_to_mat_eq size) g u v) in * by lia.
    destruct (Znth u (Znth v (@graph_to_symm_mat size g)) <? Znth v upd_pq_state) eqn: bool.
    (*smaller, updated: u is the new parent*)
      rewrite Z.ltb_lt in bool. split. rewrite eformat_symm. apply eformat_adj. auto.
      split. exists (Zlength popped_vertices). split. rewrite Zlength_app, Zlength_cons, Zlength_nil.
      split. apply Zlength_nonneg. lia. rewrite Znth_app2 by lia. rewrite Z.sub_diag, Znth_0_cons.
      split. auto. rewrite find_notIn by auto. rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
      intros.
      assert (v <> u). unfold not; intros. subst v. apply n. apply in_or_app; right; left; auto.
      rewrite sublist_same in H9. 2: auto. 2: { rewrite find_notIn, Z.add_0_r. auto. auto. }
      apply in_app_or in H9; destruct H9.
      rewrite eformat_symm, <- (@graph_to_mat_eq size) by lia.
      unfold upd_pq_state in bool.
      rewrite upd_Znth_diff in bool. 2: replace (Zlength pq_state) with size; lia.
      2: replace (Zlength pq_state) with size; lia. 2: auto.
      rewrite Hinv_6 in bool. 2: lia. destruct (in_dec V_EqDec v popped_vertices).
      exfalso. apply n. apply in_or_app; left; auto.
      rewrite Hinv_5 in bool by lia.
      (*now check whether Znth v parents is size or lower.
        If < size, use Hinv_7 to show that eformat(u0,v) must be bigger than parents.
        If size, use Hinv_8 to derive that eformat(u0,v) is invalid.
        *)
      assert (Htmp: Znth v parents <= size). apply Hinv_4. lia. apply Z.le_lteq in Htmp; destruct Htmp.
      assert (elabel g (eformat (v, Znth v parents)) <= elabel g (eformat (u0, v))). { apply (Hinv_7 v). lia.
        split. apply Hinv_4. lia. lia. rewrite find_notIn, Z.add_0_r, sublist_same. auto. auto. auto.
        unfold not; intros; apply n; apply in_or_app; left; auto.
      }
      apply (Z.le_trans _ (elabel g (eformat (v, Znth v parents)))). lia. lia.
      (*Znth v parents = size. So elabel = inf, meaning it should not be connected to u0 by Hinv_8*)
      assert (~ evalid g (eformat (u0, v))). {
        unfold not; intros. rewrite <- eformat_adj in H12.
        assert (~ adjacent g u0 v). apply Hinv_8. lia. lia.
        rewrite find_notIn, Z.add_0_r by auto. rewrite sublist_same by auto. auto.
        contradiction.
      }
      apply (invalid_edge_weight g) in H12.
      replace (elabel g (eformat (u0, v))) with inf by trivial.
      rewrite graph_to_mat_eq by lia. apply (weight_inf_bound).
      (*u0 = u.*)
      destruct H9. 2: contradiction. subst u0.
      rewrite eformat_symm. apply Z.eq_le_incl. reflexivity.
    (*case not smaller, so parent remains the same. Use Hinv_7*)
    assert (Htmp: 0 <= Znth v parents < size). apply H6.
    apply Hinv_7 in Htmp. 2: lia. destruct Htmp. destruct H10 as [[j [? ?]] ?].
    split. auto. split. exists j. split. rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
    split. rewrite Znth_app1 by lia. apply H11.
    destruct H11. apply (Z.lt_le_trans _ (find popped_vertices v 0)). auto. apply find_app_le.
    intros. rewrite find_notIn in H13 by auto. rewrite sublist_same in H13. 2: auto. 2: rewrite Z.add_0_r; auto.
    apply in_app_or in H13. destruct H13. apply H12. rewrite find_notIn. rewrite Z.add_0_r, sublist_same by auto.
    auto. unfold not; intros; apply n. apply in_or_app; left; auto.
    destruct H13. 2: contradiction. subst u0.
    (*use bool*)
    unfold upd_pq_state in bool. rewrite Z.ltb_ge in bool.
    destruct (V_EqDec u v).
      (*v=u.*)
      hnf in e; subst v. rewrite upd_Znth_same in bool.
      2: replace (Zlength pq_state) with size; lia.
      pose proof (weight_inf_bound g (eformat (u, u))). rewrite <- (@graph_to_mat_eq size) in H13 by lia.
      lia.
      (*v<>u*)
      unfold RelationClasses.complement, Equivalence.equiv in c. rewrite upd_Znth_diff in bool.
      2: replace (Zlength pq_state) with size; lia. 2: replace (Zlength pq_state) with size; lia.
      2: auto.
      rewrite Hinv_6 in bool by lia. destruct (in_dec V_EqDec v popped_vertices). exfalso; apply n; apply in_or_app; left; auto.
      rewrite Hinv_5 in bool by lia.
      rewrite graph_to_mat_eq in bool by lia. apply bool.
    (*finally, non adjacent*)
    replace (Znth v parents') with (Znth v parents). 2: symmetry; apply Hinv2_1; auto.
    replace (Znth v parents') with (Znth v parents) in H6. 2: symmetry; apply Hinv2_1; auto.
    destruct (Hinv_7 v H5 H6). destruct H10 as [[j [? ?]] ?].
    split. auto. split. exists j. split.
    rewrite Zlength_app. rewrite Zlength_cons, Zlength_nil. lia.
    split. rewrite app_Znth1 by lia. apply H11.
    destruct H11. apply (Z.lt_le_trans _ (find popped_vertices v 0)). auto. apply find_app_le.
    intros. rewrite find_notIn in H13 by auto. rewrite Z.add_0_r, sublist_same in H13 by auto.
    apply in_app_or in H13. destruct H13. apply H12.
    rewrite find_notIn. rewrite Z.add_0_r, sublist_same by auto.
    auto. unfold not; intros; apply n. apply in_or_app; left; auto.
    destruct H13. 2: contradiction. subst u0.
    (*but elabel g (eformat (u,v)) = inf because it's invalid*)
    assert (~ evalid g (eformat (u,v))). unfold not; intros; apply H8. rewrite eformat_adj; auto.
    apply (invalid_edge_weight g) in H13.
    repeat rewrite <- (@graph_to_mat_eq size) by lia. replace (Znth u (Znth v (@graph_to_symm_mat size g))) with inf.
    rewrite graph_to_mat_eq by lia. apply weight_inf_bound.
    rewrite <- (@graph_to_mat_eq size) in H13 by lia.
    symmetry. assumption.
  }
  assert (Hheavy2: forall v : Z, 0 <= v < size -> Znth v parents' = size ->
    forall u0 : V, In u0 (sublist 0 (find (popped_vertices +:: u) v 0) (popped_vertices +:: u)) ->
    ~ adjacent g u0 v). {
    intros. destruct (in_dec V_EqDec v (popped_vertices+::u)).
    apply in_app_or in i; destruct i.
    rewrite find_app_In1 in H7 by auto. rewrite sublist_app1 in H7.
    2: pose proof (find_lbound popped_vertices v 0); lia.
    2: { rewrite find_ubound, Z.add_0_r. apply Z.le_refl. }
    apply Hinv_8. lia. 2: auto.
    replace (Znth v parents) with (Znth v parents'). auto. apply Hinv2_1. lia.
    right; apply in_or_app; left; auto.
    (*v=u, pretty much same deal*)
    destruct H8. 2: contradiction. subst v. rewrite find_app_notIn1, find_cons, Z.add_0_r in H7 by auto.
    rewrite sublist_app1 in H7. 2: { pose proof (Zlength_nonneg popped_vertices). split. lia. auto. }
    2: apply Z.le_refl.
    (*rewrite sublist_same in H7 by auto.*)
    apply Hinv_8. lia. replace (Znth u parents) with (Znth u parents'); auto.
    rewrite find_notIn_0; auto.
    (*v unpopped, means u0 in popped or u0=u. Former: Hinv_8. Latter:?*)
    rewrite find_notIn, Z.add_0_r, sublist_same in H7 by auto.
    apply in_app_or in H7; destruct H7.
    destruct (adjacent_dec g u v).
    replace (Znth v parents') with (if elabel g (eformat (u, v)) <? Znth v upd_pq_state then u else Znth v parents) in H6.
    2: { symmetry; apply Hinv2_2; auto. }
    rewrite <- (@graph_to_mat_eq size) in H6 by lia. destruct (Znth u (Znth v (@graph_to_symm_mat size g)) <? Znth v upd_pq_state).
    assert (vvalid g u). apply adjacent_requires_vvalid in H8. apply H8. rewrite vert_bound in H9. lia.
    apply Hinv_8. lia. lia. rewrite find_notIn_0, sublist_same; auto.
    unfold not; intros; apply n; apply in_or_app; left; auto.
    (*not adjacent: rewrite parents' into parents*)
    replace (Znth v parents') with (Znth v parents) in H6. 2: { symmetry; apply Hinv2_1. lia. auto. }
    apply Hinv_8. lia. lia. rewrite find_notIn_0, sublist_same; auto.
    unfold not; intros; apply n; apply in_or_app; left; auto.
    (*u0=u*)
    destruct H7. 2: contradiction. subst u0.
    destruct (adjacent_dec g u v). 2: auto.
    replace (Znth v parents') with (if elabel g (eformat (u, v)) <? Znth v upd_pq_state then u else Znth v parents) in H6.
    2: { symmetry; apply Hinv2_2; auto. }
    rewrite <- (@graph_to_mat_eq size) in H6 by lia. destruct (Znth u (Znth v (@graph_to_symm_mat size g)) <? Znth v upd_pq_state) eqn:bool.
    assert (vvalid g u). apply adjacent_requires_vvalid in H7. apply H7. rewrite vert_bound in H8. lia.
    rewrite eformat_adj, evalid_inf_iff, <- (@graph_to_mat_eq size) in H7 by lia.
    rewrite Z.ltb_ge in bool. unfold upd_pq_state in bool.
    rewrite upd_Znth_diff in bool. rewrite Hinv_6 in bool by lia.
    destruct (in_dec V_EqDec v popped_vertices). exfalso; apply n; apply in_or_app; left; auto.
    rewrite Hinv_5 in bool by lia.
    replace (elabel g (eformat (v, Znth v parents))) with inf in bool. lia.
    symmetry; apply (invalid_edge_weight g).
    unfold not; intros. apply eformat_evalid_vvalid in H8. destruct H8. rewrite H6 in H9. rewrite vert_bound in H9. lia.
    replace (Zlength pq_state) with size; lia.
    replace (Zlength pq_state) with size; lia.
    unfold not; intros; subst v. apply n; apply in_or_app; right; left; auto.
  }
  assert (Hweight: forall v u1 u2 : V,
          In v (popped_vertices +:: u) ->
          0 <= Znth v parents' < size ->
          vvalid g u2 ->
          In u1 (sublist 0 (find (popped_vertices +:: u) v 0) (popped_vertices +:: u)) ->
          ~ In u2 (sublist 0 (find (popped_vertices +:: u) v 0) (popped_vertices +:: u)) ->
          elabel g (eformat (v, Znth v parents')) <= elabel g (eformat (u1, u2))
  ). { intros.
    assert (0 <= v < size). {
      apply in_app_or in H5. destruct H5. rewrite <- (vert_bound g). apply Hpopped_vvalid. auto.
      destruct H5. 2: contradiction. subst u; auto. }
    replace (Znth v parents') with (Znth v parents) in *. 2: { symmetry; apply (Hinv2_1 v); auto. }
    apply in_app_or in H5. destruct H5.
    (*case was already in popped vertices*)
    rewrite find_app_In1 in H8, H9 by auto. rewrite sublist_app1 in H8, H9.
      2: pose proof (find_lbound popped_vertices v 0); lia.
      2: { pose proof (find_ubound popped_vertices v 0). rewrite Z.add_0_r in H11. auto. }
      2: pose proof (find_lbound popped_vertices v 0); lia.
      2: { pose proof (find_ubound popped_vertices v 0). rewrite Z.add_0_r in H11. auto. }
    apply Hinv_12; auto.
    (*case v = u*)
    destruct H5. 2: contradiction. subst v.
    assert ((sublist 0 (find (popped_vertices +:: u) u 0) (popped_vertices +:: u)) =
      (popped_vertices)).
    { rewrite find_app_notIn1, find_cons, Z.add_0_r by auto.
         rewrite sublist_app1, sublist_same. auto. auto. auto.
          pose proof (Zlength_nonneg popped_vertices). split. lia. auto.
          apply Z.le_refl.
    } rewrite H5 in H9, H8.
    (*make use of Hu_min
      case u2 = u: then apply Hheavy, done (guess it wasn't useless after all)
      case u2 <> u: then by Hu_min, Znth u pq_state <= Znth u2 pq_state
        u2 is unpopped, so by Hinv_6, Znth u2 pq_state = Znth v keys
        u2 can't be r, so by Hinv_5, Znth v keys = elabel g (eformat (u2, Znth u2 parents))
        ===> Znth u pq_state <= elabel g (eformat (u2, Znth u2 parents))
        using Hheavy again? and Z.le_trans, Znth u pq_state <= elabel g (eformat (u1, u2))
        subcase u = r a.k.a. popped_vertices = []: then contradiction on u1 being in empty
        Then Znth u pq_state = Znth v keys = elabel g (eformat (u,Znth u parents)). Apply
    *)
    destruct (V_EqDec u2 u). hnf in e. subst u2.
    assert ((forall u0 : V,
          In u0 (sublist 0 (find (popped_vertices +:: u) u 0) (popped_vertices +:: u)) ->
          elabel g (eformat (u, Znth u parents')) <= elabel g (eformat (u0, u)))).
    apply Hheavy; lia. rewrite Hu_parents in H11. apply H11. rewrite H5. auto.
    rewrite vert_bound in H7. assert (vvalid g u1). apply Hpopped_vvalid; auto. rewrite vert_bound in H11.
    assert (0 <= Znth u2 parents <= size). apply Hinv_4; lia. destruct H12.
    apply Z.le_lteq in H13. destruct H13.
    2: { assert (~ adjacent g u1 u2). apply Hinv_8. lia. lia.
          rewrite find_notIn, Z.add_0_r, sublist_same by auto. auto.
          rewrite eformat_adj in H14. apply (invalid_edge_weight g) in H14.
          replace (elabel g (eformat (u1, u2))) with inf
                                                     by trivial. apply weight_inf_bound. }
    (*u2 <> u*) unfold RelationClasses.complement, Equivalence.equiv in c.
    assert (Znth u pq_state <= Znth u2 pq_state). apply Hu_min; lia.
    rewrite (Hinv_6 u2) in H14 by lia. destruct (in_dec V_EqDec u2 popped_vertices). contradiction.
    clear n. rewrite Hinv_5 in H14.
    assert (elabel g (eformat (u2, Znth u2 parents)) <= elabel g (eformat (u1,u2))).
      apply Hinv_7. lia. lia. rewrite find_notIn, Z.add_0_r, sublist_same by auto. auto. 2: auto.
    apply (Z.le_trans _ (elabel g (eformat (u2, Znth u2 parents)))). 2: auto.
    apply (Z.le_trans _ (Znth u pq_state)). 2: auto.
    clear H14 H15.
    rewrite Hinv_6 by lia. destruct (in_dec V_EqDec u popped_vertices). contradiction.
    rewrite Hinv_5 by lia. apply Z.le_refl.
  }
  (*now split into cases*)
  apply Z.le_lteq in H4. destruct H4.
  ++ (*adde case*)
  assert (vvalid mst' u). apply vert_bound. lia.
  assert (vvalid mst' (Znth u parents)). apply vert_bound. lia.
  assert (evalid g (eformat (u,(Znth u parents)))). apply Hinv_7; lia.
  assert (Hfst: vvalid mst' (fst (eformat (u,(Znth u parents))))). {
    destruct (Z.le_ge_cases u (Znth u parents)). rewrite eformat1; simpl; auto.
    rewrite eformat2; simpl; auto.
  }
  assert (Hsnd: vvalid mst' (snd (eformat (u,(Znth u parents))))). {
    destruct (Z.le_ge_cases u (Znth u parents)). rewrite eformat1; simpl; auto.
    rewrite eformat2; simpl; auto.
  }
  assert (Hfst_le_snd: (fst (eformat (u,Znth u parents))) <= (snd (eformat (u,Znth u parents)))). {
    destruct (Z.le_ge_cases u (Znth u parents)). rewrite eformat1; simpl; auto.
    rewrite eformat2; simpl; auto.
  }
  assert (Int.min_signed <= elabel g (eformat (u,(Znth u parents))) < inf). {
    split. apply weight_representable. apply evalid_inf_iff; auto.
  }
  assert (Hu_evalid: ~ evalid mst' (eformat (u,(Znth u parents)))). {
    unfold not; intros. apply (Hinv_11 u (Znth u parents)).
    auto. rewrite eformat_adj. auto.
  }
  assert (Huparents_popped: In (Znth u parents) popped_vertices). {
    assert (exists i : Z, 0 <= i < Zlength (popped_vertices) /\
      Znth i (popped_vertices) = Znth u parents /\ i < find popped_vertices u 0).
    apply Hinv_7; lia. destruct H9 as [i [? [? ?]]]. rewrite <- H10. apply Znth_In. lia.
  }
  assert (Huparents_unpopped: ~ In (Znth u parents) unpopped_vertices). {
    apply (NoDup_app_not_in V popped_vertices). apply (Permutation_NoDup (l:=VList g)).
    apply Permutation_sym; apply Hinv_3. apply NoDup_VList. auto.
  }
  set (adde_u:=adde mst' (fst (eformat (u,Znth u parents))) (snd (eformat (u,Znth u parents))) Hfst Hsnd Hfst_le_snd (elabel g (eformat (u,(Znth u parents)))) H8).
  Exists (adde_u).
  Exists (finGraph adde_u).
  Exists parents' keys' pq_state' (popped_vertices+::u) (remove V_EqDec u unpopped_vertices).
  assert (HM: exists M : UAdjMatGG, minimum_spanning_forest M g /\ is_partial_lgraph adde_u M). {
    destruct Hinv_13 as [M [Hmsf_M Hpartial_M]]. pose proof (finGraph M).
    destruct (evalid_dec M (eformat (u, Znth u parents))).
    ****
      exists M. split. auto. apply adde_partial_lgraph; auto. rewrite <- surjective_pairing; auto.
      rewrite <- surjective_pairing. symmetry. apply Hmsf_M; auto.
    ****
      set (a:=eformat (u, Znth u parents)) in *.
      (*find a corresponding edge b in M, show that elabel g a <= elabel g b
        Then do a swap
      *)
      assert (connected M (Znth u parents) u). apply Hmsf_M. apply adjacent_connected. exists a.
        split. apply (evalid_strong_evalid g); auto.
        rewrite (edge_src_fst g), (edge_dst_snd g).
        unfold a; destruct (Z.le_ge_cases u (Znth u parents)). rewrite eformat1 by (simpl; auto).
        simpl. right. auto.
        rewrite eformat2 by (simpl; auto). simpl. left; auto.
      destruct H9 as [p ?].
      (*for convenience's sake, simplify*)
      apply (connected_by_upath_exists_simple_upath) in H9. clear p. destruct H9 as [p [? ?]].
      (*since Znth u parents is in popped and u isn't, use the partition to find a v1 v2*)
      pose proof (finGraph M) as fM.
      assert (exists l, fits_upath M l p). apply connected_exists_list_edges in H9; auto. destruct H11 as [l Hl].
      assert (exists v1 v2, In v1 p /\ In v2 p /\ In v1 popped_vertices /\ ~ In v2 popped_vertices /\ (exists e, adj_edge M e v1 v2 /\ In e l)).
        apply (path_partition_checkpoint2 M popped_vertices p l (Znth u parents) u); auto.
      destruct H11 as [v1 [v2 [? [? [? [? ?]]]]]].
      destruct H15 as [b [Hb Hbl]]. assert (b = eformat (v1, v2)). {
        destruct Hmsf_M. destruct H15. destruct H15. destruct H18. destruct H18. destruct H20. apply (H20 v1 v2 b (eformat (v1,v2))).
        split. auto. apply eformat_adj'. rewrite <- eformat_adj. exists b; auto.
      } subst b. assert (evalid M (eformat (v1,v2))). apply Hb.
      assert (In v2 unpopped_vertices).
        destruct (Hpopped_or_unpopped v2). rewrite vert_bound, <- (vert_bound M).
        apply eformat_evalid_vvalid in H15; apply H15. contradiction. auto.
      set (b:= eformat (v1,v2)) in *. clear Hb. assert (Hbl': In b l) by auto.
      apply (fits_upath_split2 M p l b (Znth u parents) u) in Hbl'; auto.
      destruct Hbl' as [p1 [p2 [l1 [l2 [Hp [Hp1p2 [Hl1 [Hl2 Hl']]]]]]]].
      assert ((sublist 0 (find (popped_vertices +:: u) u 0) (popped_vertices +:: u)) = popped_vertices). {
        rewrite find_app_notIn1, find_cons, Z.add_0_r by auto.
        rewrite sublist_app1, sublist_same. auto. auto. auto.
        pose proof (Zlength_nonneg popped_vertices). split. lia. auto.
        apply Z.le_refl.
      }
      assert (elabel g a <= elabel g b). {
        unfold b; unfold a. rewrite <- Hu_parents. apply Hweight; auto.
        apply in_or_app; right; left; auto. rewrite Hu_parents; lia.
        all: rewrite H17; auto.
      } clear H17.
      assert (~ evalid mst' b). {
        unfold not; intros. rewrite <- EList_evalid in H17.
        apply (Permutation_in (l':=(map (fun v : Z => eformat (v, Znth v parents))
              (filter (fun v : Z => Znth v parents <? size) popped_vertices)))) in H17.
        apply list_in_map_inv in H17. destruct H17 as [x [? ?]]. rewrite filter_In in H19. destruct H19.
        assert (In (Znth x parents) popped_vertices). {
          rewrite H17 in H15. apply eformat_evalid_vvalid in H15. do 2 rewrite vert_bound in H15.
          assert ((exists i : Z,
            0 <= i < Zlength popped_vertices /\
            Znth i popped_vertices = Znth x parents /\ i < find popped_vertices x 0) /\
           (forall u : V,
            In u (sublist 0 (find popped_vertices x 0) popped_vertices) ->
            elabel g (eformat (x, Znth x parents)) <= elabel g (eformat (u, x)))). apply Hinv_7.
          apply H15. apply H15. destruct H21. clear H22. destruct H21 as [i [? [? ?]]].
          rewrite <- H22; apply Znth_In. lia.
        }
        (*now compare v1, v2, x, Znth x parents*)
        unfold b in H17. apply eformat_eq in H17. destruct H17; destruct H17; subst v1; subst v2; contradiction.
        apply Hinv_9.
      }
      clear Hinv_1 Hinv_2 Hinv_3 Hinv_4 Hinv_5 Hinv_6 Hinv_7 Hinv_8 Hinv_9 Hinv_10 Hinv_11 Hinv_12.
      clear Hinv2_1 Hinv2_2 Hinv2_3 Hparents_bound Hkeys' Hpq_state' Hheavy Hheavy2 Hweight.
      clear Hpopped_or_unpopped Hpopped_vvalid Hunpopped_vvalid Hu_not_popped Hu_unpopped Hu_min HZlength_parents HZlength_keys HZlength_pq_state Hu_parents Hu_keys Hu_pq_state Huparents_popped Huparents_unpopped.
      set (remove_b:= eremove M b). (*huh, how come I don't need to provide evalid b?*)
      assert (Ha_fst_vvalid: vvalid remove_b (fst a)). {
        unfold a; simpl. destruct (Z.le_ge_cases u (Znth u parents)).
        rewrite eformat1 by auto; simpl. rewrite vert_bound; lia.
        rewrite eformat2 by auto; simpl. rewrite vert_bound; lia.
      }
      assert (Ha_snd_vvalid: vvalid remove_b (snd a)). {
        unfold a; simpl. destruct (Z.le_ge_cases u (Znth u parents)).
        rewrite eformat1 by auto; simpl. rewrite vert_bound; lia.
        rewrite eformat2 by auto; simpl. rewrite vert_bound; lia.
      }
      assert (Ha_fst_le_snd: fst a <= snd a). {
        unfold a; destruct (Z.le_ge_cases u (Znth u parents)).
        rewrite eformat1; simpl; auto.
        rewrite eformat2; simpl; auto.
      }
      set (w:=elabel g a).
      assert (Ha_weight_bound: Int.min_signed <= w < inf). {
        split. apply weight_representable. apply evalid_inf_iff; auto.
      }
      set (swap:=adde remove_b (fst a) (snd a) Ha_fst_vvalid Ha_snd_vvalid Ha_fst_le_snd w Ha_weight_bound).
      assert (Hadde_partial_swap: is_partial_lgraph adde_u swap). {
        unfold is_partial_lgraph; split. split. 2: split3.
        intros. rewrite vert_bound; rewrite vert_bound in H19. lia.
        intros. simpl. simpl in H19. simpl. unfold graph_gen.addValidFunc, graph_gen.removeValidFunc in *.
        destruct H19. left. split. apply Hpartial_M. auto. unfold not; intros; subst e. contradiction. right; auto.
        intros. rewrite (edge_src_fst swap); rewrite (edge_src_fst adde_u); auto.
        intros. rewrite (edge_dst_snd swap); rewrite (edge_dst_snd adde_u); auto.
        unfold preserve_vlabel, preserve_elabel; split; intros.
        destruct vlabel. destruct vlabel. auto.
        simpl. simpl in H19. unfold graph_gen.addValidFunc in H19. unfold graph_gen.update_elabel.
        rewrite <- surjective_pairing.
        unfold EquivDec.equiv_dec. destruct (E_EqDec a e). unfold w. auto.
        unfold RelationClasses.complement, Equivalence.equiv in c. destruct H19.
        destruct (E_EqDec e b). hnf in e0; subst e. contradiction.
        apply Hpartial_M; auto.
        rewrite <- surjective_pairing in H19; symmetry in H19; contradiction.
      }
      assert (NoDup l). apply (simple_upath_list_edges_NoDup M p l); auto.
      assert (~ In b l1). { rewrite Hl' in H19.
        assert (forall y, In y l1 -> ~ In y ([b] ++l2)). apply NoDup_app_not_in; auto.
        unfold not; intros. apply H20 in H21. apply H21. apply in_or_app; left; left; auto.
      }
      assert (~ In b l2). { rewrite Hl' in H19. apply NoDup_app_r in H19.
        unfold not; intros. apply (NoDup_app_not_in E [b] l2) in H21; auto. left; auto.
      }
      assert (Hp1l1_remove: fits_upath remove_b l1 p1). { apply (fits_upath_transfer' p1 l1 M).
        intros. do 2 rewrite vert_bound; split; auto.
        intros. simpl. unfold graph_gen.removeValidFunc.
        split. apply (fits_upath_evalid M p1 l1); auto. unfold not; intros; subst e; contradiction.
        intros. simpl. auto.
        intros. simpl. auto.
        auto.
      }
      assert (Hp2l2_remove: fits_upath remove_b l2 p2). { apply (fits_upath_transfer' p2 l2 M).
        intros. do 2 rewrite vert_bound; split; auto.
        intros. simpl. unfold graph_gen.addValidFunc, graph_gen.removeValidFunc.
        split. apply (fits_upath_evalid M p2 l2); auto. unfold not; intros; subst e; contradiction.
        intros. simpl. auto.
        intros. simpl. auto.
        auto.
      }
      assert (Hp1p2': (connected_by_path remove_b p1 (Znth u parents) (fst b) /\ connected_by_path remove_b p2 (snd b) u) \/
        (connected_by_path remove_b p1 (Znth u parents) (snd b) /\ connected_by_path remove_b p2 (fst b) u)). {
        rewrite (edge_src_fst M), (edge_dst_snd M) in Hp1p2.
        destruct Hp1p2; [left | right].
        destruct H22. split. split. apply (fits_upath_valid_upath remove_b p1 l1); auto. apply H22.
        split. apply (fits_upath_valid_upath remove_b p2 l2); auto. apply H23.
        destruct H22. split. split. apply (fits_upath_valid_upath remove_b p1 l1); auto. apply H22.
        split. apply (fits_upath_valid_upath remove_b p2 l2); auto. apply H23.
      }
      assert (labeled_spanning_uforest swap g). {
        assert (is_partial_lgraph swap g). {
          assert (Hedge_valid: forall e, evalid swap e -> evalid g e).
          intros. simpl in H22. unfold graph_gen.addValidFunc, graph_gen.removeValidFunc in H22. destruct H22.
          destruct H22. apply Hmsf_M. auto. rewrite <- surjective_pairing in H22. subst e. auto.
          split. split. 2: split3.
          intros. rewrite vert_bound; rewrite vert_bound in H22. lia. auto.
          intros. rewrite (edge_src_fst swap), (edge_src_fst g); auto.
          intros. rewrite (edge_dst_snd swap), (edge_dst_snd g); auto.
          unfold preserve_vlabel, preserve_elabel; split; intros. destruct vlabel; destruct vlabel; auto.
          simpl. unfold graph_gen.update_elabel, EquivDec.equiv_dec. rewrite <- surjective_pairing.
          simpl in H22. unfold graph_gen.addValidFunc, graph_gen.removeValidFunc in H22.
          destruct (E_EqDec a e). hnf in e0; subst e. unfold w; auto.
          unfold RelationClasses.complement, Equivalence.equiv in c. destruct H22.
          destruct H22. destruct (E_EqDec e b). hnf in e0; subst e. contradiction.
          apply Hmsf_M; auto.
          symmetry in H22; rewrite <- surjective_pairing in H22; contradiction.
        }
        assert (uforest' swap). {
          assert (uforest' remove_b /\ ~ connected remove_b (src M b) (dst M b)). {
            apply remove_edge_uforest'. apply Hmsf_M. auto. }
          destruct H23. rewrite (edge_src_fst M), (edge_dst_snd M) in H24.
          apply add_edge_uforest'; auto.
          unfold not; intros; destruct H25 as [pa ?]. apply H24. clear H24.
          destruct Hp1p2'.
          ++destruct H24. apply (connected_trans _ _ (Znth u parents)). apply connected_symm; exists p1; auto.
            apply (connected_trans _ _ u). unfold a in H25. destruct (Z.le_ge_cases u (Znth u parents)).
            rewrite eformat1 in H25 by auto. apply connected_symm; exists pa; apply H25.
            rewrite eformat2 in H25 by auto. exists pa; apply H25.
            apply connected_symm; exists p2; apply H26.
          ++destruct H24. apply (connected_trans _ _ u). exists p2; auto.
            apply (connected_trans _ _ (Znth u parents)). unfold a in H25. destruct (Z.le_ge_cases u (Znth u parents)).
            rewrite eformat1 in H25 by auto. exists pa; apply H25.
            rewrite eformat2 in H25 by auto. apply connected_symm; exists pa; apply H25.
            exists p1; auto.
        }
        assert (Hremove_a: ~ evalid remove_b a). { unfold not; intros. apply n.
          simpl in H24. unfold graph_gen.removeValidFunc in H24. apply H24. }
        assert (Hswap_a: evalid swap a). { simpl. rewrite <- surjective_pairing.
          unfold graph_gen.addValidFunc. right; auto. }
        assert (Hconnected_b: connected swap (fst b) (snd b)). {
          destruct Hp1p2'; destruct H24.
          ++apply (connected_trans _ _ (Znth u parents)).
          apply connected_symm; exists p1. split. 2: apply H24.
          apply add_edge_valid_upath. rewrite <- surjective_pairing; auto. apply H24.
          apply (connected_trans _ _ u). apply adjacent_connected. rewrite eformat_adj, eformat_symm. auto.
          apply connected_symm; exists p2. split. 2: apply H25.
          apply add_edge_valid_upath. rewrite <- surjective_pairing; auto. apply H25.
          ++apply (connected_trans _ _ u).
          exists p2. split. 2: apply H25.
          apply add_edge_valid_upath. rewrite <- surjective_pairing; auto. apply H25.
          apply (connected_trans _ _ (Znth u parents)). apply adjacent_connected. rewrite eformat_adj; auto.
          exists p1. split. 2: apply H24.
          apply add_edge_valid_upath. rewrite <- surjective_pairing; auto. apply H24.
        } clear Hp1p2' Hp1p2.
        split. split. apply H22. split. auto.
        (*spanning*) { unfold spanning; intros x y.
          split; intros. 2: apply (is_partial_lgraph_connected swap); auto.
          apply Hmsf_M in H24.
          destruct H24 as [p' ?]. apply (connected_by_upath_exists_simple_upath) in H24.
          clear p'. destruct H24 as [p' [? ?]].
          assert (exists l', fits_upath M l' p'). apply valid_upath_exists_list_edges. apply H24.
          destruct H26 as [l' ?]. assert (NoDup l'). apply (simple_upath_list_edges_NoDup M p'); auto.
          clear H H0 H1.
          destruct (in_dec E_EqDec b l').
          ++ (*b is in l', must take detour*)
          assert (In b l'); auto. apply (fits_upath_split2 M p' l' b x y) in H; auto.
          destruct H as [p1x [p2y [l1x [l2y [? [? [? [? ?]]]]]]]]. subst l'; subst p'.
          rewrite (edge_src_fst M), (edge_dst_snd M) in H0 by auto.
          assert (~ In b l1x). { unfold not; intros. apply (NoDup_app_not_in _ l1x ([b]++l2y) H27 b) in H. apply H. apply in_or_app; left; left; auto. }
          assert (~ In b l2y). { apply NoDup_app_r in H27. apply (NoDup_app_not_in _ [b] l2y H27 b). left; auto. }
          destruct H0; destruct H0.
          ++++
          apply (connected_trans _ _ (fst b)). exists p1x. split. 2: apply H0. apply add_edge_valid_upath.
            rewrite <- surjective_pairing; auto. apply (remove_edge_valid_upath _ _ _ l1x); auto. apply H0.
          apply (connected_trans _ _ (snd b)); auto.
          exists p2y. split. 2: apply H30. apply add_edge_valid_upath. rewrite <- surjective_pairing; auto.
          apply (remove_edge_valid_upath _ _ _ l2y); auto. apply H30.
          ++++
          apply (connected_trans _ _ (snd b)). exists p1x. split. 2: apply H0. apply add_edge_valid_upath.
            rewrite <- surjective_pairing; auto. apply (remove_edge_valid_upath _ _ _ l1x); auto. apply H0.
          apply (connected_trans _ _ (fst b)); apply connected_symm; auto.
          apply connected_symm. exists p2y. split. 2: apply H30. apply add_edge_valid_upath. rewrite <- surjective_pairing; auto.
          apply (remove_edge_valid_upath _ _ _ l2y); auto. apply H30.
          ++ (*b isn't in l', transfer path*)
          exists p'. split. 2: apply H24. apply add_edge_valid_upath. rewrite <- surjective_pairing; auto.
          apply (remove_edge_valid_upath _ _ _ l'); auto. apply H24.
        }
        (*preserve labels*) unfold preserve_vlabel, preserve_elabel; split; intros.
        destruct vlabel; destruct vlabel; auto.
        simpl; simpl in H24. unfold graph_gen.addValidFunc, graph_gen.removeValidFunc in H24.
        unfold graph_gen.update_elabel, EquivDec.equiv_dec.
        rewrite <- surjective_pairing. rewrite <- surjective_pairing in H24.
        destruct (E_EqDec a e). hnf in e0. subst e. unfold w; auto.
        unfold RelationClasses.complement, Equivalence.equiv in c. destruct H24. 2: symmetry in H24; contradiction.
        destruct H24. destruct (E_EqDec e b). hnf in e0; contradiction. apply Hmsf_M; auto.
      }
      exists swap. split; auto. apply (msf_if_le_msf' swap M g); auto.
      unfold sum_DE, DEList. pose proof (finGraph swap) as fswap.
      rewrite (map_ext_in (elabel swap) (elabel g)).
      rewrite (map_ext_in (elabel M) (elabel g)).
      rewrite (fold_left_comm _ (map (elabel g) (EList swap)) (map (elabel g) (a::(remove E_EqDec b (EList M))))).
      simpl.
      (**) {
        set (k:=EList M).
        rewrite fold_left_accum_Zadd.
        rewrite fold_left_Zadd_map_remove. 2: unfold k; rewrite EList_evalid; auto. 2: unfold k; apply NoDup_EList.
        apply (Z.le_trans _ (fold_left Z.add (map (elabel g) k) 0 - elabel g b + elabel g b)).
        apply Zplus_le_compat_l. auto.
        rewrite Z.sub_add. apply Z.eq_le_incl. (*and... I can't reflexivity!*)
        apply fold_left_comm. intros; lia.
        apply Permutation_map. unfold k. apply NoDup_Permutation. apply NoDup_EList. apply NoDup_EList.
        intros. do 2 rewrite EList_evalid. split; intros; auto.
      }
      intros; lia.
      apply Permutation_map. { apply NoDup_Permutation. apply NoDup_EList.
        apply NoDup_cons. unfold not; intros. rewrite remove_In_iff in H23. destruct H23.
        rewrite EList_evalid in H23. contradiction.
        apply nodup_remove_nodup. apply NoDup_EList.
        intros. rewrite EList_evalid; simpl; unfold graph_gen.addValidFunc, graph_gen.removeValidFunc.
        rewrite remove_In_iff, EList_evalid, <- surjective_pairing. split; intros; destruct H23; auto.
      }
      { intros. rewrite EList_evalid in H23. apply Hmsf_M; auto. }
      {  intros. rewrite EList_evalid in H23. apply H22; auto. }
  }
  assert (Hpartial: is_partial_lgraph adde_u g). {
    apply adde_partial_lgraph. auto. rewrite <- surjective_pairing; auto. rewrite <- surjective_pairing; auto. }
  assert (Huforest_adde: uforest' adde_u). {
    apply add_edge_uforest'; auto.
    unfold not; intros. destruct (Z.le_ge_cases u (Znth u parents)).
      ****
      rewrite eformat1 in *; try (simpl; lia).
      destruct H9 as [p [? [? ?]]]. destruct p. inversion H11.
      destruct p. inversion H11; inversion H12. subst v.
      rewrite H15 in Hu_unpopped; contradiction.
      destruct H9. inversion H11. subst v.
      apply (Hinv_11 u v0). auto. apply H9.
      ****
      rewrite eformat2 in *; try (simpl; lia).
      simpl in H9. apply connected_symm in H9.
      destruct H9 as [p [? [? ?]]]. destruct p. inversion H11.
      destruct p. inversion H11; inversion H12. subst v.
      rewrite H15 in Hu_unpopped; contradiction.
      destruct H9. inversion H11. subst v.
      apply (Hinv_11 u v0). auto. apply H9.
  }
  assert (Hu_new: evalid adde_u (eformat (u, Znth u parents))). {
    simpl. unfold graph_gen.addValidFunc. right; rewrite <- surjective_pairing. auto. }
  assert (Hsrc: src adde_u (eformat (u, Znth u parents)) = fst (eformat (u, Znth u parents))). {
    apply (edge_src_fst adde_u). }
  assert (Hdst: dst adde_u (eformat (u, Znth u parents)) = snd (eformat (u, Znth u parents))). {
    apply (edge_dst_snd adde_u). }
  assert (Hnot_adj: forall u0 v : V, In u0 (remove V_EqDec u unpopped_vertices) -> ~ adjacent adde_u u0 v). {
    intros. rewrite remove_In_iff in H9; destruct H9.
    assert (~ adjacent mst' u0 v). apply Hinv_11. auto.
    unfold not; intros. destruct H12 as [e ?]. destruct (E_EqDec (eformat (u,Znth u parents)) e).
    hnf in e0. subst e.
    destruct H12. rewrite Hsrc, Hdst in H13.
    destruct (Z.le_ge_cases u (Znth u parents)).
      rewrite eformat1 in H13 by (simpl; lia). simpl in H13.
      destruct H13; destruct H13. symmetry in H13; contradiction.
      subst u0. contradiction.
      rewrite eformat2 in H13 by (simpl; lia). simpl in H13.
      destruct H13; destruct H13. subst u0; contradiction.
      symmetry in H15; contradiction.
    unfold RelationClasses.complement, Equivalence.equiv in c. apply H11.
    exists e. apply add_edge_adj_edge2 in H12; auto.
    rewrite <- surjective_pairing; auto.
  }
  assert (Hconnnected: (forall u0 v : V,
    In u0 (popped_vertices +:: u) ->
    In v (popped_vertices +:: u) -> connected g u0 v <-> connected adde_u u0 v)). {
    intros. apply in_app_or in H9; apply in_app_or in H10. destruct H9; destruct H10.
    ****(*both in popped vertices, reuse invariant*)
        split; intros.
        apply Hinv_10 in H11; auto. apply add_edge_connected; auto.
        rewrite <- surjective_pairing; auto.
        apply (is_partial_lgraph_connected adde_u); auto.
    ****(*v=u*) destruct H10. 2: contradiction. subst v.
        split; intros.
        (*g -> adde*)
        (* u0 is popped, so is Znth u parents, thus use invariant on them by adding eformat (u, Znth u parents) to the path
            Then add it again to go back to u*)
        apply (connected_trans adde_u u0 (Znth u parents) u).
        apply add_edge_connected. rewrite <- surjective_pairing. auto.
        rewrite <- Hinv_10; auto. apply (connected_trans g u0 u).
        auto. apply adjacent_connected. rewrite eformat_adj. apply H7.
        apply connected_symm. apply adjacent_connected. rewrite eformat_adj. auto.
        (*adde -> g*)
        apply (is_partial_lgraph_connected adde_u); auto.
    ****(*u0=u, repeat of above*) destruct H9. 2: contradiction. subst u0. rename H10 into H9.
        split; intros.
        apply (connected_trans adde_u u (Znth u parents) v).
        apply adjacent_connected. rewrite eformat_adj. auto.
        apply add_edge_connected. rewrite <- surjective_pairing; auto.
        rewrite <- Hinv_10; auto.
        apply (connected_trans g (Znth u parents) u).
        apply adjacent_connected. rewrite eformat_adj, eformat_symm. apply H7. auto.
        apply (is_partial_lgraph_connected adde_u); auto.
    ****destruct H9. 2: contradiction. destruct H10. 2: contradiction. subst u0. subst v.
        split; intros; apply connected_refl; rewrite vert_bound; lia.
  }
  time "end of pop loop (adde_u) (did not record original):" entailer!.
  clear H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 Pv_out HPv_out Pv_out0 Pv_key HPv_key Pv_key0.

  (*permutation of EList*)
    apply (Permutation_trans (l':=(eformat (u,Znth u parents))::(EList mst'))).
    apply Permutation_sym.
    { apply NoDup_Permutation. apply NoDup_cons. rewrite EList_evalid; auto. apply NoDup_EList. apply NoDup_EList.
      intros; split; intros. rewrite EList_evalid. simpl. unfold graph_gen.addValidFunc. destruct H9.
      rewrite <- surjective_pairing. right; symmetry; auto. left; rewrite EList_evalid in H9; auto.
      rewrite EList_evalid in H9; simpl in H9. unfold graph_gen.addValidFunc in H9; destruct H9.
      right; rewrite EList_evalid; auto. left; symmetry; auto. rewrite <- surjective_pairing in H9; auto.
    }
    apply (Permutation_trans (l':=(eformat (u, Znth u parents)) :: (map (fun v : Z => eformat (v, Znth v parents))
       (filter (fun v : Z => Znth v parents <? size) (popped_vertices))))).
    { apply Permutation_cons. auto. apply Hinv_9. }
    apply (Permutation_trans (l':=(map (fun v : Z => eformat (v, Znth v parents))
       (filter (fun v : Z => Znth v parents <? size) (popped_vertices)))+::(eformat (u, Znth u parents)))).
    { apply Permutation_cons_append. }
    replace (map (fun v : Z => eformat (v, Znth v parents))
       (filter (fun v : Z => Znth v parents <? size) popped_vertices) +:: 
     (eformat (u, Znth u parents))) with (map (fun v : Z => eformat (v, Znth v parents'))
       (filter (fun v : Z => Znth v parents' <? size) (popped_vertices +:: u))). apply Permutation_refl.
    replace [eformat (u,Znth u parents)] with (map (fun v : Z => eformat (v, Znth v parents)) [u]). 2: { simpl; auto. }
    rewrite <- list_append_map.
    replace (filter (fun v : Z => Znth v parents' <? size) (popped_vertices +:: u)) with (filter (fun v : Z => Znth v parents <? size) (popped_vertices +:: u)).
    2: {
      apply filter_ext_in. intros. replace (Znth a parents) with (Znth a parents'). auto.
      apply Hinv2_1. 2: right; auto. apply in_app_or in H9; destruct H9.
      rewrite <- (vert_bound g). apply Hpopped_vvalid; auto.
      destruct H9. 2: contradiction. subst a; lia.
    }
    replace (filter (fun v : Z => Znth v parents <? size) popped_vertices +:: u) with (filter (fun v : Z => Znth v parents <? size) (popped_vertices +:: u)).
    2: { rewrite filter_app. simpl. destruct (Znth u parents <? size) eqn: bool. auto.
      rewrite Z.ltb_ge in bool; lia. }
    apply map_ext_in; intros. rewrite filter_In in H9. destruct H9.
    replace (Znth a parents) with (Znth a parents'). auto.
    apply Hinv2_1.
    rewrite <- (vert_bound g). apply in_app_or in H9. destruct H9.
    apply Hpopped_vvalid; auto.
    destruct H9. 2: contradiction. subst a. apply Hunpopped_vvalid; auto.
    right; auto.
  ++ (*Znth u keys = inf. Implies u has no other vertices from the mst that can connect to it. Thus, no change to graph*)
  Exists mst' fmst' parents' keys' pq_state' (popped_vertices+::u) (remove V_EqDec u unpopped_vertices).
  assert (Permutation (EList mst')
      (map (fun v : Z => eformat (v, Znth v parents'))
         (filter (fun v : Z => Znth v parents' <? size) (popped_vertices +:: u)))). {
    replace (filter (fun v : Z => Znth v parents' <? size) (popped_vertices +:: u)) with
      (filter (fun v : Z => Znth v parents' <? size) (popped_vertices)).
    2: { rewrite filter_app. simpl. destruct (Znth u parents' <? size) eqn: bool.
    rewrite Z.ltb_lt in bool; lia.
    rewrite app_nil_r; auto. }
    replace (filter (fun v : Z => Znth v parents' <? size) popped_vertices) with
      (filter (fun v : Z => Znth v parents <? size) popped_vertices).
    2: { apply filter_ext_in. intros.
      replace (Znth a parents) with (Znth a parents'). auto.
      apply Hinv2_1. rewrite <- (vert_bound g). apply Hpopped_vvalid; auto.
      right; apply in_or_app; left; auto. }
    replace (map (fun v : Z => eformat (v, Znth v parents'))
     (filter (fun v : Z => Znth v parents <? size) popped_vertices)) with
      (map (fun v : Z => eformat (v, Znth v parents))
     (filter (fun v : Z => Znth v parents <? size) popped_vertices)). apply Hinv_9.
    apply map_ext_in. intros. rewrite filter_In in H5. destruct H5.
      replace (Znth a parents) with (Znth a parents'). auto.
      apply Hinv2_1. rewrite <- (vert_bound g). apply Hpopped_vvalid; auto.
      right; apply in_or_app; left; auto.
  }
  assert (Hconnected: forall u0 v : V,
    In u0 (popped_vertices +:: u) ->
    In v (popped_vertices +:: u) -> connected g u0 v <-> connected mst' u0 v). {
    intros. apply in_app_or in H6; apply in_app_or in H7.
    destruct H6; destruct H7.
    ****(*both in popped_vertices*)apply Hinv_10; auto.
    ****(*v=u*) destruct H7. 2: contradiction. subst v.
      (*hm in this case, because Znth u parents = inf, NOTHING in popped_vertices should be connected in g or mst?*)
      split; intros.
      (*get a contradiction about ~connected g u0 u:
        thoughts: destruct p:=the path to u0 u.
        assert exists a v1 v2, both in p /\ In v1 popped /\ In v2 unpopped /\ adj g v1 v2
      *)
      destruct H7 as [p ?].
      apply (path_partition_checkpoint g popped_vertices unpopped_vertices p u0 u) in H7; auto.
      destruct H7 as [v1 [v2 [? [? [? [? ?]]]]]].
      (*
        Znth v2 pq_state = keys, because it is unpopped
        Znth v2 keys >= Znth u keys = inf, because u is popped first
        Then Znth v2 parents =size using Hinv_7 and stuff
        but that violates Hinv_8
      *)
      assert (0 <= v2 < size). rewrite <- (vert_bound g); apply Hunpopped_vvalid; auto.
      assert (Hv2_notin: ~ In v2 popped_vertices). {
      apply (NoDup_app_not_in V unpopped_vertices). apply (Permutation_NoDup (l:=popped_vertices++unpopped_vertices)).
      apply Permutation_app_comm. apply (Permutation_NoDup (l:=VList g)). apply Permutation_sym; apply Hinv_3.
      apply NoDup_VList. auto.
      }
      assert (Znth v2 parents = size). {
        assert (0<=Znth v2 parents <= size). apply Hinv_4; auto.
        destruct H13. apply Z.le_lteq in H14. destruct H14. 2: auto. exfalso.
        assert (Znth v2 pq_state = Znth v2 keys). rewrite Hinv_6 by lia.
          destruct (in_dec V_EqDec v2 popped_vertices). contradiction. auto.
        assert (Znth u pq_state = Znth u keys). rewrite Hinv_6 by lia.
          destruct (in_dec V_EqDec u popped_vertices). contradiction. auto.
        assert (Znth u keys <= Znth v2 keys). rewrite <- H15, <- H16. apply Hu_min; lia.
        assert (Znth v2 keys < inf). rewrite Hinv_5 by lia.
          apply (evalid_meaning g). apply Hinv_7; lia.
        (*now so Znth u keys = inf*)
        destruct popped_vertices. contradiction.
        assert( Znth u keys = elabel g (eformat (u,Znth u parents))). rewrite Hinv_5 by lia. auto.
        rewrite H19 in H17. replace (elabel g (eformat (u, Znth u parents))) with inf in H17. lia.
        symmetry; apply (invalid_edge_weight g).
        unfold not; intros. rewrite H4 in H20. apply eformat_evalid_vvalid in H20. destruct H20.
        rewrite vert_bound in H21; lia.
      }
      exfalso. apply (Hinv_8 v2 H12 H13 v1).
      rewrite find_notIn, Z.add_0_r, sublist_same. auto. auto. auto.
      auto. auto.
      (*mst' -> g*) apply connected_symm in H7. destruct H7 as [p [? [? ?]]]. destruct p. inversion H8.
      inversion H8. destruct p. inversion H9. subst v. subst u0. apply connected_refl. rewrite vert_bound; lia.
      subst v. destruct H7. exfalso. apply (Hinv_11 u v0); auto.
    ****(*u0=u, which is repeat of above*) destruct H6. 2: contradiction. subst u0. rename H7 into H6.
      split; intros.
      (*g -> mst'*)
      apply connected_symm in H7. destruct H7 as [p ?].
      apply (path_partition_checkpoint g popped_vertices unpopped_vertices p v u) in H7; auto.
      destruct H7 as [v1 [v2 [? [? [? [? ?]]]]]].
      (*
        Znth v2 pq_state = keys, because it is unpopped
        Znth v2 keys >= Znth u keys = inf, because u is popped first
        Then Znth v2 parents =size using Hinv_7 and stuff
        but that violates Hinv_8
      *)
      assert (0 <= v2 < size). rewrite <- (vert_bound g); apply Hunpopped_vvalid; auto.
      assert (Hv2_notin: ~ In v2 popped_vertices). {
      apply (NoDup_app_not_in V unpopped_vertices). apply (Permutation_NoDup (l:=popped_vertices++unpopped_vertices)).
      apply Permutation_app_comm. apply (Permutation_NoDup (l:=VList g)). apply Permutation_sym; apply Hinv_3.
      apply NoDup_VList. auto.
      }
      assert (Znth v2 parents = size). {
        assert (0<=Znth v2 parents <= size). apply Hinv_4; auto.
        destruct H13. apply Z.le_lteq in H14. destruct H14. 2: auto. exfalso.
        assert (Znth v2 pq_state = Znth v2 keys). rewrite Hinv_6 by lia.
          destruct (in_dec V_EqDec v2 popped_vertices). contradiction. auto.
        assert (Znth u pq_state = Znth u keys). rewrite Hinv_6 by lia.
          destruct (in_dec V_EqDec u popped_vertices). contradiction. auto.
        assert (Znth u keys <= Znth v2 keys). rewrite <- H15, <- H16. apply Hu_min; lia.
        assert (Znth v2 keys < inf). rewrite Hinv_5 by lia.
          apply (evalid_meaning g). apply Hinv_7; lia.
        (*now so Znth u keys = inf*)
        destruct popped_vertices. contradiction.
        assert( Znth u keys = elabel g (eformat (u,Znth u parents))). rewrite Hinv_5 by lia. auto.
        rewrite H19 in H17. replace (elabel g (eformat (u, Znth u parents))) with inf in H17. lia.
        symmetry; apply (invalid_edge_weight g).
        unfold not; intros. rewrite H4 in H20. apply eformat_evalid_vvalid in H20. destruct H20.
        rewrite vert_bound in H21; lia.
      }
      exfalso. apply (Hinv_8 v2 H12 H13 v1).
      rewrite find_notIn, Z.add_0_r, sublist_same. auto. auto. auto.
      auto. auto.
      (*mst' -> g*) destruct H7 as [p [? [? ?]]]. destruct p. inversion H8.
      inversion H8. destruct p. inversion H9. subst v0. subst v. apply connected_refl. rewrite vert_bound; lia.
      subst v0. destruct H7. exfalso. apply (Hinv_11 u v1); auto.
    ****(*both=u*)destruct H6. 2: contradiction. destruct H7. 2: contradiction. subst u0; subst v.
    split; intros; apply connected_refl; rewrite vert_bound; lia.
  }
  assert (Hnot_adj: forall u0 v : V, In u0 (remove V_EqDec u unpopped_vertices) -> ~ adjacent mst' u0 v). {
    intros. apply Hinv_11. rewrite remove_In_iff in H6; apply H6.
  }
  time "End of pop loop (same msf) (originally 150s):" entailer!.
  }
  { (*break*) forward. (*no more vertices in queue*)
    assert (Hempty: @isEmpty inf pq_state = Vone). {
      destruct (@isEmptyTwoCases inf pq_state);
      rewrite H1 in H0; simpl in H0; now inversion H0.
    } clear H0.
    rewrite (@isEmptyMeansInf inf pq_state) in Hempty.
    rename Hempty into H0. rewrite Forall_forall in H0.
    assert (Permutation popped_vertices (VList mst')). {
      apply NoDup_Permutation.
      apply Permutation_sym, Permutation_NoDup, NoDup_app_l in Hinv_3. auto. apply NoDup_VList.
      apply NoDup_VList. intros; split; intros.
      apply VList_vvalid. rewrite vert_bound. rewrite <- (vert_bound g). apply Hpopped_vvalid; auto.
      rewrite VList_vvalid, vert_bound, <- (vert_bound g), vert_bound in H1.
      assert (Znth x pq_state = (if in_dec V_EqDec x popped_vertices then inf + 1 else Znth x keys)). apply Hinv_6; auto.
      destruct (in_dec V_EqDec x popped_vertices). auto. exfalso. rewrite Hinv_5 in H2.
      assert (Znth x pq_state > inf). apply H0. apply Znth_In. rewrite HZlength_pq_state. auto. 2: auto.
      rewrite H2 in H3. pose proof (weight_inf_bound g (eformat (x, Znth x parents))).
      (*how now brown cow, I can't lia*)
      apply Zgt_not_le in H3. contradiction.
    }
    Exists mst'. Exists fmst'. Exists popped_vertices. Exists parents. Exists keys.
    (*SEP matters*)
    replace (map Vint (map Int.repr pq_state)) with (repeat (Vint (Int.repr (inf + 1))) (Z.to_nat size)). 2: {
      apply list_eq_Znth. do 2 rewrite Zlength_map. rewrite Zlength_repeat; lia.
      intros. rewrite Zlength_repeat in H2 by lia.
      rewrite Znth_repeat_inrange by lia. rewrite Znth_map. 2: rewrite Zlength_map; lia.
      rewrite Znth_map by lia. rewrite Hinv_6 by lia.
      destruct (in_dec V_EqDec i popped_vertices). auto.
      exfalso; apply n. apply (Permutation_in (l:=VList mst')). apply Permutation_sym; auto.
      rewrite VList_vvalid, vert_bound; auto.
    }
    replace (map (fun x : V =>
      if in_dec V_EqDec x popped_vertices then Vint (Int.repr 1) else Vint (Int.repr 0))
     (nat_inc_list (Z.to_nat size))) with (repeat (Vint (Int.repr 1)) (Z.to_nat size)). 2: {
      apply list_eq_Znth. rewrite Zlength_map, Zlength_repeat, nat_inc_list_Zlength, Z2Nat.id by lia; auto.
      intros. rewrite Zlength_repeat in H2 by lia. rewrite Znth_repeat_inrange by lia.
      rewrite Znth_map. 2: rewrite nat_inc_list_Zlength, Z2Nat.id; lia.
      rewrite nat_inc_list_i. 2: rewrite Z2Nat.id; lia.
      destruct (in_dec V_EqDec i popped_vertices). auto.
      exfalso; apply n. apply (Permutation_in (l:=VList mst')). apply Permutation_sym; auto.
      rewrite VList_vvalid, vert_bound; auto.
    }
    assert (spanning mst' g). {
      unfold spanning; intros.
      split; intros. assert (vvalid g u /\ vvalid g v). apply connected_vvalid; auto. destruct H3.
      rewrite vert_bound, <- (vert_bound mst'), <- VList_vvalid in H3, H4.
      apply Hinv_10; auto.
      apply (Permutation_in (l:=VList mst')). apply Permutation_sym; auto. apply H3.
      apply (Permutation_in (l:=VList mst')). apply Permutation_sym; auto. apply H4.
      assert (vvalid mst' u /\ vvalid mst' v). apply connected_vvalid; auto. destruct H3.
      rewrite <- VList_vvalid in H3, H4.
      apply Hinv_10; auto.
      apply (Permutation_in (l:=VList mst')). apply Permutation_sym; auto. apply H3.
      apply (Permutation_in (l:=VList mst')). apply Permutation_sym; auto. apply H4.
    }
    time entailer!. (*was 55 seconds without PROP*)
  }
}
(*POST-LOOP*) {
clear Hstarting_keys HZlength_starting_keys starting_keys.
Intros mst fmst popped_vertices parents keys.
rename H into Hinv_1; rename H0 into Hinv_2;
rename H1 into Hinv_3; rename H2 into Hinv_4;
rename H3 into Hinv_5; rename H4 into Hinv_6;
rename H5 into Hinv_7; rename H6 into Hinv_8;
rename H7 into Hinv_9; rename H8 into Hinv_10.
(*Do the minimum proof here*)
assert (labeled_spanning_uforest mst g). {
  split. split. apply Hinv_1. split. apply Hinv_2. apply Hinv_7.
  split. unfold preserve_vlabel; intros. destruct vlabel. destruct vlabel. auto.
  unfold preserve_elabel; intros. apply Hinv_1. auto.
}
assert (minimum_spanning_forest mst g). {
  destruct Hinv_10 as [M [? ?]].
  apply (partial_lgraph_spanning_mst mst M g); auto.
}
assert (Permutation (EList mst)
          (map (fun v : Z => eformat (v, Znth v parents))
             (filter (fun v : Z => Znth v parents <? size) (nat_inc_list (Z.to_nat size))))). {
apply (Permutation_trans (l':= (map (fun v : Z => eformat (v, Znth v parents))
              (filter (fun v : Z => Znth v parents <? size) popped_vertices)))).
auto. apply Permutation_map. apply NoDup_Permutation.
apply NoDup_filter. apply (Permutation_NoDup (l:=VList mst)). apply Permutation_sym; auto. apply NoDup_VList.
apply NoDup_filter. apply nat_inc_list_NoDup.
intros. do 2 rewrite filter_In. rewrite nat_inc_list_in_iff by auto. rewrite Z2Nat.id by lia.
split; intros; destruct H1; split; auto.
apply (Permutation_in (l':=VList mst)) in H1. 2: auto. rewrite VList_vvalid, vert_bound in H1. lia.
apply (Permutation_in (l:=VList mst)). apply Permutation_sym; auto. rewrite VList_vvalid, vert_bound; lia.
}
freeze FR := (data_at _ _ _ v_out)
               (data_at _ _ _ (pointer_val_val parent_ptr))
               (data_at _ _ _ v_key)
               (SpaceAdjMatGraph' _ _ _).
        forward_call (Tsh, priq_ptr, size, (repeat (inf + 1) (Z.to_nat size))).
entailer!.
thaw FR.
forward.
Exists mst fmst parents.
(*change from popped_vertices to nat_inc_list*)
Transparent size.
entailer!.
Global Opaque size.
}
(*huh, where did I forget this*) rewrite map_repeat; auto.
Qed.

End NoRootPrimProof.
