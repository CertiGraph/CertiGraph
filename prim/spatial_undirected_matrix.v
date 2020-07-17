Require Import VST.veric.SeparationLogic. (*hm interesting, they have a separate sublist definition*)
Require Import VST.floyd.proofauto.
Require Import RamifyCoq.floyd_ext.share.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.FiniteGraph.
Require Import RamifyCoq.graph.undirected_graph.
Require Import RamifyCoq.prim.MatrixUGraph.
Require Import RamifyCoq.prim.prim.
Require Import RamifyCoq.lib.List_ext.

Local Open Scope logic.

Definition vertex_type := tint.

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.

Definition eformat (e: E) := if fst e <=? snd e then e else (snd e, fst e).

Lemma eformat1: forall (e: E), fst e <= snd e -> eformat e = e.
Proof. unfold eformat; intros. rewrite Zle_is_le_bool in H; rewrite H. auto. Qed.

Lemma eformat2: forall (e: E), snd e < fst e -> eformat e = (snd e, fst e).
Proof. unfold eformat; intros. rewrite <- Z.leb_gt in H; rewrite H. auto. Qed.

(*When these are unfolded in the goal and I destruct evalid_dec, I can get the hypothesis but the if... doesn't simplify

Definition elabel_inf (g: MatrixUGraph) (e: E) := if evalid_dec g e then elabel g e else inf.

Definition elabel_inf_symm (g: MatrixUGraph) (e: E) :=
  if evalid_dec g (eformat e) then elabel g (eformat e) else inf.
*)
Definition vert_rep_symm (g : MatrixUGraph) (v : V): list Z :=
  map (elabel g) (map (fun x => eformat (v,x)) (nat_inc_list (Z.to_nat SIZE))).

(* from Graph to list (list Z) *)
Definition graph_to_symm_mat (g : MatrixUGraph) : list (list Z) :=
  map (vert_rep_symm g) (nat_inc_list (Z.to_nat SIZE)).

Lemma graph_to_mat_symmetric:
  forall (g: MatrixUGraph) i j, 0 <= i < j -> j < SIZE ->
    (Znth i (Znth j (graph_to_symm_mat g))) = (Znth j (Znth i (graph_to_symm_mat g))).
Proof.
unfold graph_to_symm_mat, vert_rep_symm; intros.
repeat rewrite Znth_map. repeat rewrite nat_inc_list_i by lia.
rewrite eformat2; simpl. rewrite eformat1; simpl. auto.
lia. lia.
all: try (rewrite nat_inc_list_Zlength, Z2Nat.id; lia).
all: rewrite Zlength_map, nat_inc_list_Zlength, Z2Nat.id; lia.
Qed.

Lemma graph_to_mat_inf:
  forall (g: MatrixUGraph) u v, sound_undirected_matrix_graph g -> 0 <= u < v -> v < SIZE -> ~ evalid g (u,v) -> Znth v (Znth u (graph_to_symm_mat g)) = inf.
Proof.
unfold graph_to_symm_mat, vert_rep_symm; intros.
repeat rewrite Znth_map. repeat rewrite nat_inc_list_i.
rewrite eformat1. apply H; auto. simpl; lia.
all: try (rewrite Z2Nat.id; lia).
all: try (rewrite nat_inc_list_Zlength, Z2Nat.id; lia).
rewrite Zlength_map, nat_inc_list_Zlength, Z2Nat.id; lia.
Qed.

(*************C related**********)

Definition list_address a index size : val :=
  offset_val (index * sizeof (tarray tint size)) a.

Definition list_rep sh size l contents_mat index :=
  let mylist := (Znth index contents_mat) in
  data_at sh (tarray tint size) (map Vint (map Int.repr mylist)) (list_address l index size).

Definition undirected_matrix sh matrix_contents gaddr : mpred :=
  iter_sepcon.iter_sepcon (list_rep sh SIZE gaddr matrix_contents)
                          (nat_inc_list (Z.to_nat (Zlength matrix_contents))).

(*isolate the "ith row"*)
Lemma graph_unfold: forall sh contents ptr i,
    0 <= i < (Zlength contents) ->
    undirected_matrix sh contents ptr =
    iter_sepcon.iter_sepcon (list_rep sh SIZE ptr contents) (*<---before*)
            (sublist 0 i (nat_inc_list (Z.to_nat (Zlength contents)))) *
    (list_rep sh SIZE ptr contents i * (*ith array*)
           iter_sepcon.iter_sepcon (list_rep sh SIZE ptr contents) (*after*)
             (sublist (i + 1) (Zlength contents) (nat_inc_list (Z.to_nat (Zlength contents))))).
Proof.
  intros. unfold undirected_matrix.
  replace (nat_inc_list (Z.to_nat (Zlength contents))) with
      (sublist 0 (Zlength contents) (nat_inc_list (Z.to_nat (Zlength contents)))) at 1.
  2: { rewrite sublist_same; trivial.
       rewrite nat_inc_list_Zlength, Z2Nat_id', Z.max_r; trivial.
       apply Zlength_nonneg.
  }
  rewrite (sublist_split 0 i (Zlength contents)),
  (sublist_split i (i+1) (Zlength contents)), (sublist_one i); try lia.
  2, 3, 4: rewrite nat_inc_list_Zlength; rewrite Z2Nat.id; lia.
  rewrite nat_inc_list_i.
  2: rewrite Z2Nat_id', Z.max_r; trivial; apply Zlength_nonneg. 
  repeat rewrite iter_sepcon.iter_sepcon_app.
  simpl. rewrite sepcon_emp. reflexivity.
Qed.