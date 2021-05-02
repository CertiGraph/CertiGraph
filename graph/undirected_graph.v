Require Import Coq.Logic.Classical.
Require Import CertiGraph.lib.List_ext.
Require Import CertiGraph.lib.EquivDec_ext.
Require Import CertiGraph.graph.graph_model.
Require Import CertiGraph.graph.graph_relation.
Require Import CertiGraph.graph.path_lemmas.
Require Import CertiGraph.graph.graph_gen.
Require Import CertiGraph.graph.FiniteGraph.

Section UNDIRECTED.

Context {V E: Type}.
Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.

Local Notation PGraph := (PreGraph V E).

(*as long as there is an edge from u to v, u and v are connected, regardless of who is the src*)
Definition adj_edge (g: PGraph) (e: E) (u v: V) :=
  strong_evalid g e /\
  ((src g e = u /\ dst g e = v) \/ (src g e = v /\ dst g e = u)).

Lemma strong_evalid_adj_edge:
forall g e, strong_evalid g e -> adj_edge g e (src g e) (dst g e).
Proof.
intros. split. auto. left; auto.
Qed.

Lemma adj_edge_sym:
forall g e u v, adj_edge g e u v -> adj_edge g e v u.
Proof.
intros. destruct H. split; auto.
destruct H0. right; auto. left; auto.
Qed.

Lemma adj_edge_vvalid:
  forall g e u v, adj_edge g e u v -> vvalid g u /\ vvalid g v.
Proof.
intros. destruct H. destruct H as [? [? ?]]. destruct H0; destruct H0.
all: subst u; subst v; split; auto.
Qed.

(*Consequently, we may not care about the exact nature of the edges*)
Definition adjacent (g: PGraph) (u v: V) := exists e: E, adj_edge g e u v.

Corollary adjacent_requires_vvalid:
  forall g u v, adjacent g u v -> vvalid g u /\ vvalid g v.
Proof.
intros. destruct H. apply (adj_edge_vvalid g x u v H).
Qed.

Lemma adjacent_symm:
  forall g u v, adjacent g u v -> adjacent g v u.
Proof.
intros. destruct H. exists x. destruct H. destruct H0.
split. apply H. right. apply H0.
split. apply H. left. apply H0.
Qed.

(*
But we may still need to pull out the edges, e.g. for labels
Problem is, because the graph is still fundamentally directed, there can be edges going a->b and b->a
So maybe we just return every such edge
But, it makes no sense having an undirected graph with more than one edge between two vertices
*)
Definition adj_edges g u v := fun e => adj_edge g e u v.

(*A bunch of helpers for convenience in handling options*)
Definition adjacent_last g (u: option V) (v: V) :=
match u with
| None => vvalid g v
| Some u' => adjacent g u' v
end.

Definition adjacent_hd g (u: V) (v: option V) :=
match v with
| None => vvalid g u
| Some v' => adjacent g u v'
end.

Definition adjacent_err g (u: option V) (v: option V) :=
match u, v with
| None, None => True
| None, Some v' => vvalid g v'
| Some u', None => vvalid g u'
| Some u', Some v' => adjacent g u' v'
end.

Lemma adjacent_last_adjacent:
  forall g u v, adjacent_last g (Some u) v <-> adjacent g u v.
Proof.
intros; split; intros; destruct H; exists x; apply H.
Qed.

Lemma adjacent_hd_adjacent:
  forall g u v, adjacent_hd g u (Some v) <-> adjacent g u v.
Proof.
intros; split; intros; destruct H; exists x; apply H.
Qed.

Lemma adjacent_err_adjacent:
  forall g u v, adjacent_err g (Some u) (Some v) <-> adjacent g u v.
Proof.
intros; split; intros; destruct H; exists x; apply H.
Qed.

Lemma adjacent_err_last:
  forall g opt_u v, adjacent_err g opt_u (Some v) -> adjacent_last g opt_u v.
Proof.
destruct opt_u; intros; apply H.
Qed.

Lemma adjacent_err_hd:
  forall g u opt_v, adjacent_err g (Some u) opt_v -> adjacent_hd g u opt_v.
Proof.
destruct opt_v; intros; apply H.
Qed.

(************UNDIRECTED PATHS************)

(*I think it makes sense to define an undirected path based on vertices,
  given the definition above. Hard to define based on edges since edges are implicitly directed*)
Definition upath := list V.

(*So the difference between here and path_lemmas, is that the directed paths are guaranteed one vertex. That's why I need the last_error*)

Fixpoint valid_upath (g: PGraph) (p: upath) : Prop :=
  match p with
    | nil => True
    | u :: nil => vvalid g u
    | u :: ((v :: _) as p') => adjacent g u v /\ valid_upath g p' (* /\ vvalid g u*)
  end.

Lemma valid_upath_tail':
  forall g p u, valid_upath g (u::p) -> valid_upath g p.
Proof.
induction p; intros.
-simpl; auto.
-simpl in H. destruct H. destruct p.
  +simpl; auto.
  +destruct H0. simpl. split. apply H0. apply H1.
Qed.

Corollary valid_upath_tail:
  forall g p, valid_upath g p -> valid_upath g (tl p).
Proof.
intros; destruct p. auto. simpl. apply (valid_upath_tail' g p v H).
Qed.

Lemma valid_upath_cons:
  forall g p u, valid_upath g p -> adjacent_hd g u (hd_error p) -> valid_upath g (u::p).
Proof.
induction p; intros.
-simpl in H0. simpl; auto.
-destruct p.
  +simpl in *. auto.
  +split. apply H0. apply H.
Qed.

Lemma valid_upath_vvalid:
  forall g p v, valid_upath g p -> In v p -> vvalid g v.
Proof.
induction p; intros. contradiction.
simpl in H0. destruct H0.
subst a. destruct p. auto. destruct H. destruct H. destruct H. destruct H.
destruct H1; destruct H1. rewrite <- H1. apply H2. rewrite <- H3; apply H2.
apply IHp. apply (valid_upath_tail' g p a H). auto.
Qed.

Lemma valid_upath_app:
  forall g p1 p2, valid_upath g p1 -> valid_upath g p2 -> adjacent_err g (last_error p1) (hd_error p2) -> valid_upath g (p1++p2).
Proof.
induction p1; intros.
-apply H0.
-destruct p1.
  +simpl. apply valid_upath_cons. apply H0. apply adjacent_err_hd. apply H1.
  +rewrite <- app_comm_cons. split. apply H. apply IHp1. apply H. apply H0. apply H1.
Qed.

Lemma hd_error_none_nil:
  forall {A:Type} (l: list A), hd_error l = None <-> l = nil.
Proof.
  intros; split; intros. destruct l. reflexivity. simpl in H. inversion H.
  rewrite H. reflexivity.
Qed.

Lemma valid_upath_app_2: (*find a better name*)
  forall g p1 p2, valid_upath g p1 -> valid_upath g p2 -> (last_error p1) = (hd_error p2) -> valid_upath g (p1++(tail p2)).
Proof.
intros. apply valid_upath_app. apply H. apply (valid_upath_tail g p2 H0).
unfold adjacent_err.
destruct (last_error p1) eqn:H2. destruct (hd_error p2) eqn:H3.
assert (v = v0) by (inversion H1; reflexivity).
destruct (hd_error (tl p2)) eqn: H5. assert (p2 = v0::v1::(tl (tl p2))).
apply hd_error_tl_repr. split. apply H3. apply hd_error_tl_repr. split. apply H5. reflexivity.
rewrite H6 in H0. destruct H0. rewrite H4. apply H0.
assert (p2 = v0::(tl p2)). apply hd_error_tl_repr. split. apply H3. reflexivity.
rewrite hd_error_none_nil in H5. unfold valid_upath in H0. rewrite H6 in H0; rewrite H5 in H0.
rewrite H4; apply H0.
inversion H1.
assert (tl p2 = nil). destruct p2. reflexivity. inversion H1. rewrite H3. simpl. trivial.
Qed.

Corollary valid_upath_concat:
  forall g p v, valid_upath g p -> adjacent_last g (last_error p) v -> valid_upath g (p+::v).
Proof.
intros. apply (valid_upath_app g p (v::nil)). apply H.
simpl. destruct (last_error p); simpl in H0. apply (adjacent_requires_vvalid g v0 v H0). apply H0.
destruct (last_error p); simpl in *; apply H0.
Qed.

Lemma valid_upath_app_split:
  forall g p p', valid_upath g (p++p') -> (valid_upath g p /\ valid_upath g p').
Proof.
induction p; intros. simpl in H. split. simpl. auto. apply H.
destruct p. destruct p'. simpl in *. split; auto. simpl in H. destruct H. destruct H. destruct H.
split. simpl. destruct H. destruct H1; destruct H1. rewrite <- H1. apply H2. rewrite <- H3. apply H2.
apply H0.
destruct H. apply IHp in H0. split. split. apply H. apply H0. apply H0.
Qed.

Lemma valid_upath_rev:
  forall g p, valid_upath g p -> valid_upath g (rev p).
Proof.
induction p; intros. auto.
simpl. apply valid_upath_concat. apply IHp. apply (valid_upath_tail' g p a H).
rewrite <- rev_hd_last. destruct p. apply H.
simpl. destruct H. apply adjacent_symm. apply H.
Qed.

(**********************CONNECTED*************)

Definition connected_by_path (g: PGraph) (p: upath) (n : V) :=
  fun n' => valid_upath g p /\ hd_error p = Some n /\ last_error p = Some n'.

Definition connected (g: PGraph) (n : V) :=
  fun n' => exists p, connected_by_path g p n n'.

Lemma connected_exists_path:
  forall (g: PGraph) u v,
    connected g u v <->
    exists p, 
      valid_upath g p /\
      hd_error p = Some u /\ last_error p = Some v.
Proof. intros; split; intros; auto. Qed.

Lemma connected_refl:
forall g v, vvalid g v -> connected g v v.
Proof.
intros. exists (v::nil). split. simpl; auto.
split; simpl; auto.
Qed.

Lemma connected_by_path_rev:
  forall g p u v, connected_by_path g p u v -> connected_by_path g (rev p) v u.
Proof.
intros. split. apply valid_upath_rev. apply H.
destruct H as [? [? ?]]. split. rewrite rev_hd_last, rev_involutive; auto.
rewrite <- rev_hd_last; auto.
Qed.

Corollary connected_symm:
  forall g u v, connected g u v -> connected g v u.
Proof.
intros. destruct H as [p ?]. exists (rev p). apply connected_by_path_rev; auto.
Qed.

Lemma connected_by_path_join:
  forall g p1 p2 u v w, (connected_by_path g p1 u v) -> (connected_by_path g p2 v w)
  -> connected_by_path g (p1++(tail p2)) u w.
Proof.
intros. destruct H as [? [? ?]]. destruct H0 as [? [? ?]].
split. apply valid_upath_app_2. apply H. apply H0.
rewrite H2, H3. reflexivity.
split. assert (p1 = u::(tl p1)). apply hd_error_tl_repr. split. apply H1. reflexivity.
rewrite H5. rewrite <- app_comm_cons. simpl. reflexivity.
destruct p2 eqn:H5. inversion H4.
destruct u0. simpl in *. rewrite <- app_nil_end. rewrite <- H4. rewrite H3. apply H2.
simpl. apply last_err_app. simpl in H4. simpl. apply H4.
Qed.

Corollary connected_trans:
  forall g u v w, connected g u v -> connected g v w -> connected g u w.
Proof.
intros. destruct H as [p1 ?]. destruct H0 as [p2 ?].
exists (p1++(tail p2)). apply (connected_by_path_join g p1 p2 u v w); auto.
Qed.

Lemma adjacent_connected:
  forall g u v, adjacent g u v -> connected g u v.
Proof.
intros. exists (u::v::nil). split. split. auto.
simpl. destruct H. destruct H. destruct H.
destruct H0; destruct H0. rewrite <- H2; apply H1. rewrite <- H0; apply H1.
split; simpl; auto.
Qed.

Lemma connected_by_path_vvalid:
  forall g p u v, connected_by_path g p u v -> vvalid g u /\ vvalid g v.
Proof.
intros. destruct H. destruct H0.
split. apply (valid_upath_vvalid g p u). auto. apply hd_error_In; auto.
apply (valid_upath_vvalid g p v). auto. apply last_error_In; auto.
Qed.

Corollary connected_vvalid:
  forall g u v, connected g u v -> vvalid g u /\ vvalid g v.
Proof.
intros. destruct H as [p ?]. apply (connected_by_path_vvalid _ _ _ _ H).
Qed.

Lemma adjacent_dec:
forall g u v, adjacent g u v \/ ~ adjacent g u v.
Proof.
  intros. tauto.
Qed.

Lemma connected_dec:
forall g u v, connected g u v \/ ~ connected g u v.
Proof.
  intros. tauto.
Qed.

Definition connected_graph (g: PGraph) := forall u v, vvalid g u -> vvalid g v -> connected g u v.

(************REASONING ABOUT A SPECIFIC LIST OF EDGES************)

Fixpoint fits_upath g (l: list E) (p: upath) :=
match l, p with
| nil, nil => True
| nil, v::nil => vvalid g v
| e::l', u::v::p' => adj_edge g e u v /\ fits_upath g l' (v::p')
| _, _ => False
end.

Lemma valid_upath_exists_list_edges:
  forall g p, valid_upath g p-> exists l, fits_upath g l p.
Proof.
induction p; intros. exists nil; simpl; auto.
destruct p. exists nil; simpl; auto.
destruct H. destruct H. apply IHp in H0. destruct H0 as [l ?].
exists (x::l). split; auto.
Qed.

Lemma valid_upath_exists_list_edges':
  forall g p, (exists l, fits_upath g l p) -> valid_upath g p.
Proof.
induction p; intros. simpl. auto.
destruct H as [l ?].
destruct p. simpl. destruct l; simpl in H; [auto | contradiction].
destruct l. simpl in H; contradiction. destruct H.
split. exists e; apply H. apply IHp.
exists l. apply H0.
Qed.

Corollary fits_upath_valid_upath:
  forall g p l, fits_upath g l p -> valid_upath g p.
Proof.
intros. apply valid_upath_exists_list_edges'. exists l; auto.
Qed.

Corollary connected_exists_list_edges:
  forall g p u v, connected_by_path g p u v -> exists l, fits_upath g l p.
Proof.
intros. destruct H. apply valid_upath_exists_list_edges. apply H.
Qed.

Corollary connected_exists_list_edges':
  forall g p u v, (forall v, In v p -> vvalid g v) -> (exists l, fits_upath g l p) ->
    hd_error p = Some u -> last_error p = Some v ->
    connected_by_path g p u v.
Proof.
intros. split. apply valid_upath_exists_list_edges'; auto. split; auto.
Qed.

Lemma fits_upath_cons:
forall g p l e v v0, fits_upath g (e::l) (v::v0::p) -> fits_upath g l (v0::p).
Proof.
intros; destruct p; destruct l.
simpl. apply H.
simpl in H. destruct H. auto.
simpl in H. destruct H. contradiction.
simpl in H. destruct H. destruct H0. simpl. split; auto.
Qed.

Lemma fits_upath_strong_evalid:
  forall g p l e, fits_upath g l p -> In e l -> strong_evalid g e.
Proof.
induction p; destruct l; intros; try contradiction.
destruct p eqn:Hp. unfold fits_upath in H. contradiction. rename l0 into p'.
destruct l eqn:Hl. unfold fits_upath in H. simpl in H; destruct H.
simpl in H0; destruct H0; try contradiction. rewrite H0 in H. destruct H. apply H.
apply in_inv in H0. destruct H0.
  unfold fits_upath in H. simpl in H; destruct H. rewrite H0 in H. destruct H. apply H.
apply fits_upath_cons in H.
apply (IHp (e1::l0)). apply H. apply H0.
Qed.

Corollary fits_upath_evalid:
  forall g p l e, fits_upath g l p -> In e l -> evalid g e.
Proof.
  intros; apply (fits_upath_strong_evalid g p l e); auto.
Qed.

Lemma fits_upath_vertex_src_In:
forall g p l e, fits_upath g l p -> In e l -> In (src g e) p.
Proof.
induction p; intros. destruct l; auto.
destruct p. destruct l; simpl in H; contradiction.
destruct l. contradiction. destruct H0.
subst e0. destruct H. destruct H. destruct H1. left; symmetry; apply H1.
right. left. symmetry; apply H1.
right. apply (IHp l). apply H. auto.
Qed.

Lemma fits_upath_vertex_dst_In:
forall g p l e, fits_upath g l p -> In e l -> In (dst g e) p.
Proof.
induction p; intros. destruct l; auto.
destruct p. destruct l; simpl in H; contradiction.
destruct l. contradiction. destruct H0.
subst e0. destruct H. destruct H. destruct H1.
right. left. symmetry; apply H1.
left; symmetry; apply H1.
right. apply (IHp l). apply H. auto.
Qed.

Lemma fits_upath_In_adj:
forall l g p e, fits_upath g l p -> In e l -> exists u v, In u p /\ In v p /\ adj_edge g e u v.
Proof.
induction l; intros.
contradiction.
destruct p. simpl in H. contradiction.
destruct p. simpl in H. contradiction.
destruct H0. subst e.
destruct H. exists v. exists v0. split. left; auto. split. right; left; auto. auto.
destruct H. destruct (IHl g (v0::p) e) as [x [y [? [? ?]]]]; auto.
exists x; exists y. split. right; auto. split. right; auto. auto.
Qed.

Lemma fits_upath_concat:
forall g p l e u, fits_upath g l p -> (exists v, last_error p = Some v /\ adj_edge g e u v) -> fits_upath g (l+::e) (p+::u).
Proof.
induction p; intros. destruct l. destruct H0 as [v [? ?]]. simpl in H0. inversion H0.
simpl in H. contradiction.
destruct p; destruct l. destruct H0 as [v [? ?]]. simpl in H0. inversion H0. subst a.
simpl. split. apply adj_edge_sym; auto. apply (adj_edge_vvalid g e u v H1).
simpl in H. contradiction.
simpl in H. contradiction.
destruct H0 as [v0 [? ?]]. destruct H. split. auto. apply IHp. auto.
exists v0. split. rewrite last_error_cons in H0; auto. unfold not; intros; inversion H3. auto.
Qed.

Lemma fits_upath_split':
forall g p l e, fits_upath g l p -> In e l ->
  exists p1 p2 l1 l2, p = p1++p2 /\
    ((last_error p1 = Some (src g e) /\ hd_error p2 = Some (dst g e)) \/ (last_error p1 = Some (dst g e) /\ hd_error p2 = Some (src g e)))
    /\ fits_upath g l1 p1 /\ fits_upath g l2 p2 /\ l = l1++(e::nil)++l2.
Proof.
induction p; intros. destruct l. contradiction. simpl in H; contradiction.
destruct p; destruct l. contradiction. simpl in H; contradiction. contradiction.
destruct H. destruct H0.
(*case e is first edge.*)
subst e0. exists (a::nil). exists (v::p). exists nil. exists l.
split. simpl. auto.
split. destruct H. destruct H0; destruct H0; subst a; subst v.
left; simpl; auto. right; simpl; auto.
split. simpl; apply (adj_edge_vvalid g e a v H). split; auto.
(*case e isn't*)
pose proof (IHp l e H1 H0); clear IHp.
destruct H2 as [p1 [p2 [l1 [l2 ?]]]]. destruct H2 as [? [? [? [? ?]]]].
exists (a::p1). exists p2. exists (e0::l1). exists l2.
split. simpl. rewrite <- H2. auto.
split. destruct H3; destruct H3.
left; split; auto. rewrite last_error_cons. apply H3. unfold not;intros. subst p1. inversion H3.
right; split; auto. rewrite last_error_cons. apply H3. unfold not; intros. subst p1. inversion H3.
split.
destruct p1. destruct H3; destruct H3; inversion H3.
assert (v = v0). inversion H2; auto. subst v0. split; auto.
split. auto.
simpl. simpl in H6. rewrite H6; auto.
Qed.

Lemma fits_upath_split2:
forall g p l e u v, connected_by_path g p u v -> fits_upath g l p -> In e l ->
  exists p1 p2 l1 l2, p = p1++p2 /\
    ((connected_by_path g p1 u (src g e) /\ connected_by_path g p2 (dst g e) v) \/ (connected_by_path g p1 u (dst g e) /\ connected_by_path g p2 (src g e) v))
    /\ fits_upath g l1 p1 /\ fits_upath g l2 p2 /\ l = l1++(e::nil)++l2.
Proof.
intros. destruct (fits_upath_split' g p l e) as [p1 ?]; auto.
destruct H2 as [p2 [l1 [l2 [? [? [? [? ?]]]]]]]. exists p1. exists p2. exists l1. exists l2.
repeat split; auto.
destruct H. destruct H7. subst p; subst l. destruct H3.
++
destruct H2. left. split. split. apply (fits_upath_valid_upath g p1 l1); auto.
split. destruct p1. inversion H2. simpl; auto. auto.
split. apply (fits_upath_valid_upath g p2 l2); auto. split.
auto. destruct p2. inversion H3. rewrite last_err_split2 in H8. auto.
++
destruct H2. right. split. split. apply (fits_upath_valid_upath g p1 l1); auto.
split. destruct p1. inversion H2. simpl; auto. auto.
split. apply (fits_upath_valid_upath g p2 l2); auto. split.
auto. destruct p2. inversion H3. rewrite last_err_split2 in H8. auto.
Qed.

Lemma fits_upath_split:
forall g p1 p2 l, fits_upath g l (p1++p2) -> exists l1 l2 l3, fits_upath g l1 p1 /\ fits_upath g l3 p2 /\ l = (l1++l2++l3).
Proof.
induction p1; intros.
rewrite app_nil_l in H. exists nil. exists nil. exists l. split. simpl; auto. split; simpl; auto.
destruct p1. destruct l. destruct p2.
exists nil; exists nil; exists nil. split. simpl; auto. split; simpl; auto.
simpl in H. contradiction.
replace ((a :: nil) ++ p2) with (a::p2) in H. 2: simpl; auto.
destruct p2. simpl in H; contradiction.
destruct H. exists nil. exists (e::nil). exists l. split; simpl; auto. apply (adj_edge_vvalid g e a v H).
destruct l. simpl in H; contradiction.
destruct H. apply IHp1 in H0. destruct H0 as [l1 [l2 [l3 [? [? ?]]]]].
exists (e::l1). exists l2. exists l3. split. split; auto. split. auto. simpl. rewrite H2. auto.
Qed.

Lemma fits_upath_rev:
forall g p l, fits_upath g l p -> fits_upath g (rev l) (rev p).
Proof.
induction p; intros. destruct l. simpl; auto. simpl in H. contradiction.
destruct p. destruct l. simpl; auto. simpl in H; contradiction.
destruct l. simpl in H; contradiction.
destruct H. simpl. simpl in IHp. apply fits_upath_concat.
apply IHp. auto.
exists v. split. apply last_err_appcons. auto.
Qed.

Lemma fits_upath_app:
forall g p1 p2 l1 l2 e u v, fits_upath g l1 p1 -> fits_upath g l2 p2 ->
  last_error p1 = Some u -> hd_error p2 = Some v -> adj_edge g e u v ->
  fits_upath g (l1++(e::nil)++l2) (p1++p2).
Proof.
induction p1; intros. inversion H1.
destruct p1. destruct l1. simpl. destruct p2. inversion H2.
simpl in H1. inversion H1. subst a. simpl in H2. inversion H2. subst v0. split; auto.
simpl in H; contradiction.
destruct l1. simpl in H; contradiction.
split. apply H.
apply (IHp1 p2 l1 l2 e u v); auto. apply H.
Qed.

Lemma fits_upath_vertex_in_path:
forall g p e l, fits_upath g l p -> In e l -> In (src g e) p /\ In (dst g e) p.
Proof.
induction p; intros. destruct l; auto.
destruct p. destruct l; [contradiction|auto]. simpl in H; contradiction.
destruct l. simpl in H; contradiction.
destruct H0. subst e0.
destruct H. destruct H. destruct H1; destruct H1; subst a; subst v.
split. left; auto. right; left; auto.
split. right; left; auto. left; auto.
assert (In (src g e) (v :: p) /\ In (dst g e) (v :: p)). apply (IHp e l). apply H. auto. destruct H1.
split; right; auto.
Qed.

Lemma fits_upath_transfer'':
forall p l g1 g2,
  (forall v, In v p -> vvalid g2 v) ->
  (forall e, In e l -> evalid g2 e) ->
  (forall e, In e l -> src g1 e = src g2 e) ->
  (forall e, In e l -> dst g1 e = dst g2 e) ->
  fits_upath g1 l p -> fits_upath g2 l p.
Proof.
induction p; intros. destruct l. auto. apply H3.
destruct l. destruct p. simpl. apply H; left; auto. simpl in H3. contradiction.
destruct p. simpl in H3. contradiction.
split.
assert (In e (e::l)). left; auto.
+ (*adjacent edge*)
  split. split. apply H0. left; auto.
  split. rewrite <- H1; auto. apply H. apply (fits_upath_vertex_src_In g1 _ (e::l) e); auto.
  rewrite <- H2; auto. apply H. apply (fits_upath_vertex_dst_In g1 _ (e::l) e); auto.
  rewrite <- H1; auto. rewrite <- H2; auto.
  destruct H3. destruct H3. auto.
+ apply (IHp l g1 g2). intros. apply H. right; auto.
  intros. apply H0. right; auto.
  intros. apply H1. right; auto.
  intros. apply H2. right; auto.
  apply H3.
Qed.

Lemma fits_upath_transfer':
forall p l g1 g2,
  (forall v, vvalid g1 v <-> vvalid g2 v) ->
  (forall e, In e l -> evalid g2 e) ->
  (forall e, evalid g1 e -> evalid g2 e -> src g1 e = src g2 e) ->
  (forall e, evalid g1 e -> evalid g2 e -> dst g1 e = dst g2 e) ->
  fits_upath g1 l p -> fits_upath g2 l p.
Proof.
induction p; intros. destruct l. auto. apply H3.
destruct l. destruct p. simpl. simpl in H3. apply H; auto. simpl in H3. contradiction.
destruct p. simpl in H3. contradiction.
destruct H3. split.
+ (*adjacent edge*)
  destruct H3. destruct H3. destruct H6. assert (evalid g2 e). apply H0. left. auto.
  split. split. apply H0. left; auto. split.
  apply H in H6. rewrite H1 in H6; auto.
  apply H in H7. rewrite H2 in H7; auto.
  rewrite H1 in H5; auto. rewrite H2 in H5; auto.
+ apply (IHp l g1 g2); auto. intros. apply H0. right; auto.
Qed.

Lemma trivial_path1:
  forall g e, strong_evalid g e ->
    connected_by_path g ((src g e)::(dst g e)::nil) (src g e) (dst g e) /\
    fits_upath g (e::nil) ((src g e)::(dst g e)::nil).
Proof.
intros. split.
split. simpl. split. exists e. split. auto. left; auto. apply H.
simpl. auto.
simpl. split. split. apply H. left; auto. apply H.
Qed.

(************REACHABLE -> CONNECTED************)

Lemma valid_path'_cons:
  forall (g: PreGraph V E) p a, valid_path' g (a::p) -> valid_path' g p.
Proof.
intros; destruct p. reflexivity.
simpl. simpl in H. destruct H. destruct H0. apply H1.
Qed.

Corollary valid_path_cons:
  forall (g: PreGraph V E) v a l, valid_path g (v,a::l) -> valid_path g (dst g a, l).
Proof.
unfold valid_path; intros. destruct H. destruct l. apply H0.
split. apply H0. apply (valid_path'_cons g (e::l) a H0).
Qed.

Lemma valid_dpath_implies_valid_upath':
  forall g p, valid_path' g p -> valid_upath g (epath_to_vpath' g p).
Proof.
intros. induction p.
simpl. trivial.
assert (valid_path' g p). apply (valid_path'_cons g p a H).
destruct p eqn:H_p. simpl. split.
exists a. split. apply H. left. split; reflexivity.
apply H.
assert (epath_to_vpath' g (a :: e :: l) = (src g a) :: epath_to_vpath' g (e::l)).
simpl. reflexivity.
rewrite H1; clear H1.
apply valid_upath_cons. apply IHp. apply H0.
assert (hd_error (epath_to_vpath' g (e :: l)) = Some (src g e)).
destruct l; reflexivity. rewrite H1.
unfold adjacent_hd. unfold adjacent. exists a.
split. apply H. left. split. reflexivity. apply H.
Qed.

Lemma valid_dpath_implies_valid_upath:
  forall g p, valid_path g p -> valid_upath g (epath_to_vpath g p).
Proof.
intros. unfold epath_to_vpath. destruct p. destruct l.
simpl. apply H. apply valid_dpath_implies_valid_upath'. apply H.
Qed.

Lemma epath_to_vpath_head:
  forall (g: PreGraph V E) p, valid_path g p -> hd_error (epath_to_vpath g p) = Some (phead p).
Proof.
intros. destruct p. destruct l.
-simpl. reflexivity.
-simpl. unfold valid_path in H. destruct H. destruct l; rewrite H; simpl; reflexivity.
Qed.

Lemma pfoot_cons:
  forall (g: PreGraph V E) l e v, valid_path g (v, e::l) -> pfoot g (v,(e::l)) = pfoot g (dst g e, l).
Proof.
intros. destruct l; simpl. reflexivity.
apply (pfoot_head_irrel l g v (dst g e) e0).
Qed.

Lemma epath_to_vpath_foot':
  forall (g: PreGraph V E) l v, valid_path g (v, l) -> last_error (epath_to_vpath g (v,l)) = Some (pfoot g (v,l)).
Proof.
unfold epath_to_vpath; induction l; intros. reflexivity.
destruct l. reflexivity. rewrite pfoot_cons. 2: auto.
assert (valid_path g (dst g a, e::l)). apply H.
rewrite <- IHl. 2: auto.
apply last_error_cons. simpl. unfold not; intros. destruct l; inversion H1.
Qed.

Corollary epath_to_vpath_foot:
  forall (g: PreGraph V E) p, valid_path g p -> last_error (epath_to_vpath g p) = Some (pfoot g p).
Proof.
destruct p. apply epath_to_vpath_foot'.
Qed.

Lemma adjacent_reachable:
  forall g u v, adjacent g u v ->
    (reachable g u v \/ reachable g v u).
Proof.
intros.
unfold adjacent, adj_edge in H.
destruct H as [e [? [[? ?] | [? ?]]]];
  [left | right];
  unfold reachable, reachable_by, reachable_by_path.
- exists (u, (e::nil)); split.
  + split; trivial.
  + unfold good_path. split; simpl.
    * split; trivial; symmetry; trivial.
    * unfold path_prop. split; trivial.
      rewrite Forall_forall; intros; split; trivial.
- exists (v, e::nil); split.
  + split; trivial.
  + unfold good_path. split; simpl.
    * split; trivial; symmetry; trivial.
    * unfold path_prop. split; trivial.
      rewrite Forall_forall; intros; split; trivial.
Qed.

Lemma reachable_implies_connected:
  forall g u v, reachable g u v -> connected g u v.
Proof.
intros. unfold reachable_by in H. destruct H. destruct H. rename x into dp.
exists (epath_to_vpath g dp). split.
apply valid_dpath_implies_valid_upath. apply H0.
destruct H0. clear H1.
destruct dp; destruct l. unfold path_ends in H; unfold phead in H; destruct H.
split; simpl. rewrite H; reflexivity.
unfold pfoot in H1. unfold pfoot' in H1. rewrite H1; reflexivity.
unfold path_ends in H. destruct H. unfold phead in H.
split. rewrite H. apply epath_to_vpath_head. rewrite <- H. apply H0.
rewrite epath_to_vpath_foot. rewrite H1. reflexivity. apply H0.
Qed.




(************(CONNECTED) COMPONENTS************)

Definition component (g: PGraph) :=
  forall u v, connected g u v. (*Here we only care about connectedness; and are using as a set*)

Definition maximal_component (g: PGraph):=
  component g /\ forall u v, connected g u v.
(*
Lemma connected_graph_component:
  forall g P, connected_graph g -> maximal_component g -> Same_set P (vvalid g).
*)

(************UFOREST************)

(*Use wiki/Bender & Williamson 2010's definition. Defining a cycle is troublesome because
1. have to deal with negations in definition of unique_simple_upath
2. we support multiple edges btwn vertices, if so are they a cycle?
For the purposes of kruskal, we need unique_simple_upath more than cycles*)

Definition simple_upath g p := valid_upath g p /\ NoDup p.

Lemma simple_upath_tail:
  forall g a p, simple_upath g (a::p) -> simple_upath g p.
Proof.
intros. destruct H. split. apply (valid_upath_tail' g p a). auto. apply NoDup_cons_1 in H0. auto.
Qed.

Lemma simple_upath_app_split:
  forall g p p', simple_upath g (p++p') -> (simple_upath g p /\ simple_upath g p').
Proof.
intros. destruct H. split; split.
apply (valid_upath_app_split _ _ _ H). apply (NoDup_app_l _ _ _ H0).
apply (valid_upath_app_split _ _ _ H). apply (NoDup_app_r _ _ _ H0).
Qed.

Lemma upath_simplifiable_edges:
  forall g p l u v, connected_by_path g p u v -> fits_upath g l p ->
    exists p' l', connected_by_path g p' u v /\ simple_upath g p' /\ incl p' p
      /\ fits_upath g l' p' /\ incl l' l.
Proof.
induction p; intros.
destruct H. destruct H1. inversion H1.
destruct p. destruct H. simpl in H. simpl in H1; destruct H1.
inversion H1; inversion H2. subst u; subst v. clear H1 H2.
destruct l. 2: { simpl in H0; contradiction. }
exists (a::nil). exists nil. split. split. simpl; auto. simpl; split; auto.
split. split. simpl; auto. apply NoDup_cons. auto. apply NoDup_nil.
unfold incl; intros; auto.
(*inductive step*)
destruct l. simpl in H0; contradiction.
destruct H as [? [? ?]]. destruct H.
assert (connected_by_path g (v0::p) v0 v). split. auto. split. apply hd_error_cons. rewrite last_error_cons in H2; auto. unfold not; intros. inversion H4.
destruct H0. apply (IHp l v0 v H4) in H5. destruct H5 as [p' ?]. destruct H5 as [l' [? [? [? [? ?]]]]].
destruct (in_dec EV a p').
(*if a is already inside p, then we take the subpath.*)
apply in_split in i. destruct i as [p1 [p2 ?]]. subst p'.
exists (a::p2). (*split l'*)
apply fits_upath_split in H8. destruct H8 as [l1 [l2 [l3 [? [? ?]]]]].
exists l3. split. split. destruct H6. apply valid_upath_app_split in H6. apply H6.
split. simpl in H1. simpl. apply H1. destruct H5. destruct H12.
rewrite last_err_split2 in H13. auto. split.
apply simple_upath_app_split in H6. apply H6. split.
unfold incl; intros. destruct H12. subst a0. left; auto.
right. apply H7. apply in_or_app. right. right. auto.
split. auto. unfold incl; intros. right. apply H9. subst l'. apply in_or_app. right. apply in_or_app. auto.
(*case where a isn't inside. Then straightforward concat*)
exists (a::p'). exists (e::l').
split. split.
destruct p'. simpl. apply (adjacent_requires_vvalid g a v0). auto.
destruct H5. destruct H10. simpl in H10. inversion H10. subst v1.
split; auto.
split. simpl in H1. simpl. auto.
destruct H5. destruct H10.
rewrite last_error_cons. auto. unfold not; intros; subst p'. inversion H10.
split. split.
destruct p'. simpl. apply (adjacent_requires_vvalid g a v0). auto.
destruct H5. destruct H10. simpl in H10. inversion H10. subst v1. split; auto.
apply NoDup_cons. auto. apply H6.
split.
unfold incl; intros. destruct H10. subst a0. left; auto. right; apply H7. auto.
split. destruct H5. destruct H10. destruct p'. inversion H10.
inversion H10. subst v1. split; auto.
unfold incl; intros. destruct H10. subst a0. left. auto. right. apply H9. auto.
Qed.

Corollary connected_by_upath_exists_simple_upath:
  forall g p u v, connected_by_path g p u v-> exists p', connected_by_path g p' u v /\ simple_upath g p'.
Proof.
intros. pose proof (connected_exists_list_edges g p u v H). destruct H0 as [l ?].
pose proof (upath_simplifiable_edges g p l u v H H0). destruct H1 as [p' [? [? [? ?]]]].
exists p'. split; auto.
Qed.

Lemma simple_upath_list_edges_NoDup:
  forall g p l, simple_upath g p -> fits_upath g l p -> NoDup l.
Proof.
induction p; intros. destruct l. apply NoDup_nil. simpl in H0; contradiction.
destruct p; destruct l. apply NoDup_nil. simpl in H0; contradiction.
simpl in H0; contradiction.
destruct H0. apply NoDup_cons.
unfold not; intros.
destruct H0. apply (fits_upath_vertex_in_path g (v::p) e) in H2.
destruct H3; destruct H3; subst a; subst v; destruct H; apply NoDup_cons_2 in H3; destruct H2; contradiction.
auto.
apply IHp. split. apply H. destruct H. apply NoDup_cons_1 in H2. auto. auto.
Qed.

Definition unique_simple_upath g :=
  (forall u v p1 p2,
  simple_upath g p1 -> connected_by_path g p1 u v ->
  simple_upath g p2 -> connected_by_path g p2 u v ->
  p1 = p2).

(*Definition we're using*)
Definition uforest' g :=
  (forall e, evalid g e -> src g e <> dst g e) /\ (*No self-cycles*)
  (forall u v e1 e2, adj_edge g e1 u v /\ adj_edge g e2 u v -> e1 = e2) /\ (*Not a multigraph, preventing internal cycles within two vertices*)
  (forall e, evalid g e -> strong_evalid g e) /\ (*with no rubbish edges. Debatable where this should go?*)
  unique_simple_upath g. (*finally, the actual forest definition*)

Lemma forest_no_self_adjacency:
  forall g e v, uforest' g -> ~ adj_edge g e v v.
Proof.
unfold not; intros. destruct H. destruct H0. destruct H0. apply H in H0.
destruct H2; destruct H2; subst v; symmetry in H4; contradiction.
Qed.

Lemma forest_edge':
  forall p l g e, uforest' g -> strong_evalid g e ->
    connected_by_path g p (src g e) (dst g e) -> fits_upath g l p ->
    In e l.
Proof.
intros. pose proof (upath_simplifiable_edges g p l (src g e) (dst g e) H1 H2).
destruct H3 as [p' [l' [? [? [? [? ?]]]]]].
pose proof (trivial_path1 g e H0). destruct H8 as [? ?].
assert (simple_upath g ((src g e)::(dst g e)::nil)). split. apply H8. apply NoDup_cons.
unfold not; intros; destruct H10. symmetry in H10. apply H in H10. contradiction. apply H0.
simpl in H10; contradiction.
apply NoDup_cons. unfold not; intros. simpl in H10; contradiction. apply NoDup_nil.
assert (p' = (src g e :: dst g e :: nil)). destruct H as [? [? [? ?]]]. apply (H13 (src g e) (dst g e)); auto.
subst p'. apply H7.
destruct l'. simpl in H6; contradiction.
destruct l'. 2: { simpl in H6. destruct H6. contradiction. }
left. destruct H9. destruct H6.
destruct H as [? [? ?]]. apply (H13 (src g e) (dst g e)). split; auto.
Qed.

(*to avoid having to keep destructing to find the unique_simple_upath def*)
Lemma uforest'_unique_simple_path:
  forall g, uforest' g -> unique_simple_upath g.
Proof. intros. apply H. Qed.

Lemma uforest'_unique_lpath:
forall p l1 l2 g, uforest' g -> simple_upath g p -> fits_upath g l1 p -> fits_upath g l2 p -> l1 = l2.
Proof.
induction p; intros. destruct l1. destruct l2. auto. simpl in H2; contradiction. simpl in H1; contradiction.
destruct p. destruct l1. destruct l2. auto. simpl in H2; contradiction. contradiction.
destruct l1. contradiction. destruct l2. contradiction.
destruct H1. destruct H2. assert (e = e0). destruct H. destruct H5. apply (H5 a v). split; auto. subst e0.
assert (l1 = l2). apply (IHp l1 l2 g); auto. apply (simple_upath_tail g a (v::p)); auto.
subst l1. auto.
Qed.

Definition bridge g e u v :=
forall p l, connected_by_path g p u v -> fits_upath g l p -> In e l.

Lemma forest_simple_bridge:
forall p l g u v, uforest' g -> connected_by_path g p u v -> simple_upath g p -> fits_upath g l p ->
forall e, In e l -> bridge g e u v.
Proof.
induction p; intros.
destruct H0. destruct H4. inversion H4.
destruct p; destruct l. contradiction. simpl in H2. contradiction. simpl in H2. contradiction.
assert (a = u). destruct H0. destruct H4. inversion H4. auto. subst a.
unfold bridge; intros.
pose proof (upath_simplifiable_edges g p0 l0 u v H4 H5). destruct H6 as [p' [l' [? [? [? [? ?]]]]]]. apply H10.
assert (p' = (u::v0::p)). assert (unique_simple_upath g). apply H. apply (H11 u v p' (u::v0::p)); auto. subst p'.
assert ((e0::l) = l'). apply (uforest'_unique_lpath (u::v0::p) (e0::l) l' g); auto. subst l'.
apply H3. (*hm, didn't need induction*)
Qed.

Lemma forest_adj_bridge:
forall g e u v, uforest' g -> adj_edge g e u v -> bridge g e u v.
Proof.
unfold bridge; intros. apply (upath_simplifiable_edges g p l u v) in H2; auto.
destruct H2 as [p' [l' [? [? [? [? ?]]]]]].
assert (fits_upath g (e::nil) (u::v::nil)). simpl. split; auto.
  apply connected_by_path_vvalid in H1; apply H1.
assert (connected_by_path g (u::v::nil) u v). apply connected_exists_list_edges'.
  apply connected_by_path_vvalid in H1.
  intros. simpl in H8. destruct H8. subst v0. apply H1. destruct H8.
  subst v0. apply H1. contradiction.
  exists (e::nil). auto.
  simpl; auto. simpl; auto.
assert (simple_upath g (u::v::nil)). split. apply H8. apply NoDup_cons.
  unfold not; intros. destruct H9. subst u.
  apply forest_no_self_adjacency in H0; auto.
  contradiction. apply NoDup_cons. auto. apply NoDup_nil.
assert (p' = (u::v::nil)). destruct H as [? [? [? ?]]]. apply (H12 u v); auto. subst p'.
apply H6. assert (l' = (e::nil)). apply (uforest'_unique_lpath (u::v::nil) _ _ g); auto.
rewrite H10. left; auto.
Qed.

Lemma fits_upath_reduced_list:
forall p l g u v, fits_upath g l p -> In u p -> In v p ->
  exists p' l', connected_by_path g p' u v /\ fits_upath g l' p' /\ incl p' p /\ incl l' l.
Proof.
induction p; intros. contradiction.
destruct p. destruct H0. destruct H1. 2: contradiction. 2: contradiction. subst u; subst v.
destruct l. simpl in H. exists (a::nil); exists nil. split.
unfold connected_by_path. split; simpl; auto.
split. simpl; auto.
unfold incl; split; intros; auto.
simpl in H; contradiction.
destruct l. simpl in H; contradiction. destruct H.
destruct H0; destruct H1.
++
subst u; subst v. exists (a::nil); exists nil. split.
unfold connected_by_path. split. simpl. apply adj_edge_vvalid in H; apply H. simpl; auto.
split. simpl. apply adj_edge_vvalid in H; apply H. simpl; auto.
unfold incl; split; intros; try contradiction. destruct H0. subst a0. left; auto. contradiction.
++
subst u. assert (exists (p' : upath) (l' : list E),
        connected_by_path g p' v0 v /\ fits_upath g l' p' /\ incl p' (v0 :: p) /\ incl l' l).
apply IHp; auto. left; auto. destruct H0 as [p' [l' [? [? [? ?]]]]].
exists (a::p'). exists (e::l'). destruct H0. destruct H6.
split. split. apply valid_upath_cons. apply H0.
rewrite H6; simpl. exists e; auto.
split. simpl; auto. rewrite last_error_cons. auto. unfold not; intros; subst p'. inversion H7.
split. destruct p'. inversion H6. simpl. split. inversion H6; subst v1; auto. auto.
unfold incl; split; intros. destruct H8. subst a0; left; auto. right; apply H4 in H8; auto.
destruct H8. subst a0; left; auto. right; apply H5 in H8; auto.
++
subst v. assert (exists (p' : upath) (l' : list E),
        connected_by_path g p' u v0 /\ fits_upath g l' p' /\ incl p' (v0 :: p) /\ incl l' l).
apply IHp; auto. left; auto. destruct H1 as [p' [l' [? [? [? ?]]]]].
exists (p'+::a). exists (l'+::e). destruct H1. destruct H6.
split. split. apply valid_upath_app. apply H1. simpl. apply adj_edge_vvalid in H; apply H.
rewrite H7; simpl. apply adjacent_symm. exists e; auto.
split. rewrite (hd_error_app _ _ u); auto. rewrite (last_err_app _ _ a); auto.
split. apply (fits_upath_app g p' (a::nil) l' nil e v0 a). auto.
simpl. apply adj_edge_vvalid in H; apply H. auto. simpl; auto.
apply adj_edge_sym; auto.
unfold incl; split; intros. apply in_app_or in H8; destruct H8. right; apply H4; auto.
destruct H8. subst a0; left; auto. contradiction.
apply in_app_or in H8; destruct H8. right; apply H5; auto. destruct H8. subst a0; left; auto. contradiction.
++
assert (exists (p' : upath) (l' : list E),
        connected_by_path g p' u v /\ fits_upath g l' p' /\ incl p' (v0 :: p) /\ incl l' l).
apply IHp; auto.
destruct H3 as [p' [l' [? [? [? ?]]]]].
exists p'; exists l'. split. auto. split. auto. unfold incl; split; intros.
right; apply H5; auto. right; apply H6; auto.
Qed.

Lemma bridge_must_be_crossed:
forall g e u v p l, bridge g e u v -> In u p -> In v p -> fits_upath g l p -> In e l.
Proof.
intros. assert (exists p' l', connected_by_path g p' u v /\ fits_upath g l' p' /\ incl p' p /\ incl l' l).
apply fits_upath_reduced_list; auto.
destruct H3 as [p' [l' [? [? [? ?]]]]].
apply H6. apply (H p' l'); auto.
Qed.

Lemma bridge_splittable:
forall p g u v e, connected_by_path g p u v -> bridge g e u v -> 
  (exists p1 p2, p = p1++p2 /\
    ((connected_by_path g p1 u (src g e) /\ connected_by_path g p2 (dst g e) v) \/
      (connected_by_path g p1 u (dst g e) /\ connected_by_path g p2 (src g e) v))
  ).
Proof.
induction p; intros. destruct H. destruct H1. inversion H1.
destruct p.
(*single vertex in path - trivial connection, no bridge exists*)
unfold bridge in H0. assert (fits_upath g nil (a::nil)). simpl. apply (valid_upath_vvalid g (a::nil)). apply H. left; auto.
apply H0 in H1; auto. contradiction.
(*proper version to look at. Destruct cases: Is e in between a::v0*)
destruct H. destruct H1. simpl in H1; inversion H1. subst a. clear H1.
destruct H. destruct H as [e' ?].
destruct (EE e e'). unfold equiv in e0. subst e'.
(*yes, e at the front.*)
destruct H. destruct H3; destruct H3; rewrite H3; rewrite H4.
exists (u::nil); exists (v0::p). split. simpl; auto.
left. split. split. simpl. rewrite <- H3. apply H. simpl; auto.
split. apply H1. split. simpl. auto. rewrite last_error_cons in H2; auto. unfold not; intros. inversion H5.
exists (u::nil); exists (v0::p). split. simpl; auto.
right. split. split. simpl. rewrite <- H4. apply H. simpl; auto.
split. apply H1. split. simpl. auto. rewrite last_error_cons in H2; auto. unfold not; intros. inversion H5.
(*no, then e should be further in*)
specialize IHp with g v0 v e.
assert (exists p1 p2 : list V,
        v0 :: p = p1 ++ p2 /\
        (connected_by_path g p1 v0 (src g e) /\ connected_by_path g p2 (dst g e) v \/
         connected_by_path g p1 v0 (dst g e) /\ connected_by_path g p2 (src g e) v)).
apply IHp. split. auto. split. simpl. auto. rewrite last_error_cons in H2; auto. unfold not; intros. inversion H3.
(*hm, I should put this as a separate lemma?*)
unfold bridge; intros. unfold bridge in H0.
assert (In e (e'::l)). apply (H0 (u::p0) (e'::l)). split. apply valid_upath_cons. apply H3.
  destruct H3. destruct H5. rewrite H5. simpl. exists e'; auto.
  split. simpl; auto. destruct H3. destruct H5. rewrite last_error_cons. auto. unfold not; intros. rewrite H7 in H5. inversion H5.
  destruct p0. destruct H3. destruct H5. inversion H5.
  destruct H3. destruct H5. simpl in H5. inversion H5. subst v1.
  split; auto.
destruct H5. unfold complement, equiv in c. symmetry in H5; contradiction. auto.
destruct H3 as [p1 [p2 [? ?]]].
exists (u::p1); exists p2. split. simpl. rewrite H3. auto.
destruct H4; destruct H4. left; split; auto.
split. apply valid_upath_cons. rewrite H3 in H1. apply (valid_upath_app_split _ _ _ H1).
destruct H4. destruct H6. rewrite H6. simpl. exists e'. auto.
split. simpl; auto. destruct H4. destruct H6. rewrite last_error_cons. auto. unfold not; intros. rewrite H8 in H6; inversion H6.
(*feels a bit finicky in that we can assume p1 <> nil. I suppose this comes from bridge*)
right; split; auto.
split. apply valid_upath_cons. rewrite H3 in H1. apply (valid_upath_app_split _ _ _ H1).
destruct H4. destruct H6. rewrite H6. simpl. exists e'. auto.
split. simpl; auto. destruct H4. destruct H6. rewrite last_error_cons. auto. unfold not; intros. rewrite H8 in H6; inversion H6.
Qed.

Definition spanning t g :=
  forall u v, connected g u v <-> connected t u v.

Lemma spanning_preserves_vertices:
forall g t v, spanning t g -> (vvalid g v <-> vvalid t v).
Proof.
intros; split; intros; pose proof (connected_refl _ v H0);
apply H in H1; apply connected_vvalid in H1; apply H1.
Qed.

Definition spanning_uforest t g :=
  is_partial_graph t g /\ (*t is a partial graph of g*)
  uforest' t /\ (*it is also a forest*)
  spanning t g. (*that is spanning...*)

Lemma NoDup_rev:
  forall {A: Type} (l: list A), NoDup l -> NoDup (rev l).
Proof.
induction l; intros. simpl; auto.
simpl. apply NoDup_app_inv. apply IHl. apply NoDup_cons_1 in H; auto.
apply NoDup_cons. unfold not; intros; contradiction. apply NoDup_nil.
intros. apply in_rev in H0. unfold not; intros. destruct H1.
subst a. apply NoDup_cons_2 in H. contradiction. contradiction.
Qed.

Lemma simple_upath_rev:
  forall g p, simple_upath g p -> simple_upath g (rev p).
Proof.
intros. split. apply valid_upath_rev; apply H. apply NoDup_rev; apply H.
Qed.

(*cycle definition from CLRS
k>0 <-> p has at least two vertices
all edges distinct <-> NoDup l
*)
Definition ucycle g p l :=
match p with
| nil => False
| u::nil => False
| u::v::p' => connected_by_path g p u u /\ fits_upath g l p /\ NoDup l
end.

Definition simple_ucycle g p l := NoDup (tl p) /\ ucycle g p l.

Lemma uforest'_no_simple_ucycles:
forall g, uforest' g -> (forall p l, valid_upath g p -> fits_upath g l p -> ~ simple_ucycle g p l).
Proof.
intros. destruct H as [Hself [Hmulti [Hstrong Hforest]]]. unfold not; intros. destruct H.
destruct p. contradiction.
destruct p. contradiction.
destruct l. contradiction.
destruct H2. destruct H2 as [_ [_ ?]]. destruct H3 as [_ ?].
simpl in H. apply NoDup_cons_2 in H3.
assert (v <> v0). unfold not; intros. subst v0. destruct H1. destruct H1. destruct H1.
apply Hself in H1. destruct H5; destruct H5; rewrite H5 in H1; rewrite H7 in H1; contradiction.
(*contradiction lies in In e l*)
destruct H1.
assert (simple_upath g (v::v0::nil)).
  split. simpl; split. exists e; auto. apply (valid_upath_vvalid _ _ _ H0). right; left; auto.
  apply NoDup_cons. unfold not; intros; destruct H6. symmetry in H6; contradiction. contradiction.
  apply NoDup_cons. auto. apply NoDup_nil.
assert (simple_upath g (v0::p)).
  split. apply valid_upath_tail in H0. simpl in H0; auto. auto.
assert ((v::v0::nil) = (rev (v0::p))). apply (Hforest v v0).
  auto. split. apply H6. split; simpl; auto.
  apply simple_upath_rev; auto.
  apply connected_by_path_rev. split. apply H7. split. simpl; auto.
  rewrite last_error_cons in H2; auto. unfold not; intros. inversion H8.
pose proof (fits_upath_rev g (v0::p) l H5). rewrite <- H8 in H9.
destruct (rev l) eqn:Hrevl. contradiction. destruct l0. 2: simpl in H9; destruct H9; contradiction.
simpl in H9. destruct H9 as [? _]. assert (e = e0). apply (Hmulti v v0). split; auto. subst e0.
apply H3. apply in_rev. rewrite Hrevl. left; auto.
Qed.

(*to be 100% close to CLRS' wording*)

Definition uforest g := (forall e, evalid g e -> strong_evalid g e) /\ (*strong evalid*)
  (forall p l, ~ simple_ucycle g p l). (*no undirected cycles*)

Definition utree g := uforest g /\ connected_graph g.

Corollary uforest'_no_simple_ucycle:
forall g p l, uforest' g -> ~ simple_ucycle g p l.
Proof.
unfold uforest, not; intros. destruct H0.
destruct p. contradiction.
destruct p. contradiction.
destruct H1 as [? [? ?]]. destruct l. contradiction.
apply (uforest'_no_simple_ucycles g H (v::v0::p) (e::l)).
apply H1. auto. split. auto. split. auto. split. auto. auto.
Qed.

Corollary uforest'_uforest:
forall g, uforest' g -> uforest g.
Proof.
unfold uforest. split. apply H. intros. apply uforest'_no_simple_ucycle. auto.
Qed.

(*The proof of the converse may be finicky, because it requires reasoning about "do this"
But I don't think the converse is unnecessary;
At most, we redefine unique_simple_upath in the no-cycle way and show that kruskal creates a tree that satisfies previous_def, thus is a unique_simple_upath
*)

Lemma uforest_no_self_loops:
forall g e, uforest g -> evalid g e -> src g e <> dst g e.
Proof.
unfold not; intros. rename H1 into H2; rename H0 into H1.
destruct H. apply (H0 (src g e :: dst g e :: nil) (e::nil)).
rewrite H2. split. simpl. apply NoDup_cons. unfold not; intros; auto. apply NoDup_nil.
unfold ucycle. assert (adj_edge g e (dst g e) (dst g e)).
  rewrite <- H2 at 1. apply strong_evalid_adj_edge. apply H. apply H1.
split. unfold connected_by_path; simpl. split. split. exists e.
auto. apply H. apply H1. auto.
split. simpl. split. auto. apply H. apply H1. auto.
apply NoDup_cons. unfold not; intros; auto. apply NoDup_nil.
Qed.

Lemma uforest_no_multigraph:
forall g (u v : V) (e1 e2 : E), uforest g ->
  adj_edge g e1 u v /\ adj_edge g e2 u v -> e1 = e2.
Proof.
intros. rename H0 into H1. destruct H.
destruct H1. destruct (EE e1 e2). hnf in e; auto.
unfold complement, equiv in c. exfalso.
apply (H0 (u::v::u::nil) (e1::e2::nil)). split.
simpl. apply NoDup_cons. unfold not; intros. destruct H3. 2: contradiction.
subst v. destruct H2. apply (uforest_no_self_loops g e2); auto. split. apply H. apply H0.
apply H2. destruct H3; destruct H3; subst u; auto.
apply NoDup_cons. unfold not; intros; auto. apply NoDup_nil.
unfold ucycle. split. unfold connected_by_path. simpl. split; auto.
split. exists e1; auto. split. apply adjacent_symm. exists e1; auto.
apply adj_edge_vvalid in H1. apply H1.
split. simpl. split. auto. split. apply adj_edge_sym; auto. apply adj_edge_vvalid in H2; apply H2.
apply NoDup_cons. unfold not; intros. destruct H3. symmetry in H3; contradiction. contradiction.
apply NoDup_cons. unfold not; intros; auto. apply NoDup_nil.
Qed.

Lemma simple_upath_self:
forall g u p, connected_by_path g p u u -> simple_upath g p -> p = (u::nil).
Proof.
intros. destruct H as [? [? ?]]. destruct p. inversion H1.
simpl in H1; inversion H1. subst v.
destruct p. auto. rewrite last_error_cons in H2. 2: unfold not; intros; inversion H3.
destruct H0. apply NoDup_cons_2 in H3. exfalso; apply H3. apply last_error_In. auto.
Qed.

Lemma split_list_In_first:
forall (l: list V) v, In v l -> exists la lb, l = la ++ v::lb /\ (forall u, In u la -> u <> v).
Proof.
induction l; intros. contradiction.
destruct H. subst v. exists nil. exists l. rewrite app_nil_l; auto.
destruct (EV a v). hnf in e. subst v.
exists nil. exists l. split. simpl; auto. unfold not; intros; contradiction.
unfold complement, equiv in c.
apply IHl in H. destruct H as [la [lb [? ?]]].
exists (a::la). exists lb. split. simpl; rewrite H; auto.
unfold not; intros. destruct H1. subst u; subst v. contradiction.
apply (H0 u); auto.
Qed.

Lemma split_list_In:
forall (l: list V) v, In v l -> exists la lb, l = la ++ v::lb.
Proof.
intros. apply split_list_In_first in H. destruct H as [la [lb [? ?]]].
exists la; exists lb; apply H.
Qed.

Lemma first_point_of_convergence_ugly:
forall l1 l2 (v: V), hd_error l1 <> hd_error l2 -> In v l1 -> In v l2 ->
  exists l1a l2a v' l1b l2b, l1 = l1a++v'::l1b /\ l2 = l2a++v'::l2b /\
  (forall u, In u l1a -> ~ In u l2a) /\ (forall u, In u l2a -> ~ In u l1a) /\ l1a <> l2a.
Proof.
induction l1; intros. contradiction.
destruct l2. contradiction.
destruct H0; destruct H1.
++
subst a; subst v0; simpl in H. contradiction.
++
subst a. apply split_list_In in H1. destruct H1 as [lx [ly ?]].
exists nil. exists (v0::lx). exists v. exists l1. exists ly.
split. rewrite app_nil_l; auto. split. simpl; rewrite H0; auto.
split. intros. contradiction.
split. unfold not; intros; auto.
unfold not; intros. inversion H1.
++
subst v0. apply split_list_In in H0. destruct H0 as [lx [ly ?]].
exists (a::lx). exists nil. exists v. exists ly. exists l2.
split. simpl; rewrite H0; auto. split. apply app_nil_l.
split. unfold not; intros. contradiction. split. intros. contradiction.
unfold not; intros; inversion H1.
++
assert (a <> v0). unfold not; intros. subst a. simpl in H. contradiction.
destruct l1. contradiction. destruct l2. contradiction.
destruct (EV v1 v2).
**
hnf in e. subst v2.
exists (a::nil). exists (v0::nil). exists v1. exists l1. exists l2.
split. simpl; auto. split. simpl; auto. split. unfold not; intros.
destruct H3. subst a. destruct H4. subst v0. all: try contradiction.
split. unfold not; intros. destruct H3. subst v0. destruct H4. subst a. all: try contradiction.
unfold not; intros. inversion H3. contradiction.
**
(*use IHL*)
unfold complement, equiv in c.
apply (IHl1 (v2::l2) v) in H1. 2: { simpl; unfold not; intros; inversion H3. contradiction. } 2: auto.
destruct H1 as [l1a [l2a [v' [l1b [l2b [? [? [? ?]]]]]]]].
rename v0 into b.
(*is a in l2a?*)
destruct (in_dec EV a l2a). apply split_list_In_first in i. destruct i as [l2a1 [l2a2 [? ?]]].
exists nil. exists (b::l2a1). exists a. exists (v1::l1). exists (l2a2++v'::l2b).
split. simpl; auto. split. rewrite H3. subst l2a.
simpl. rewrite app_comm_cons. rewrite <- (app_assoc (b::l2a1) (a::l2a2)). simpl. auto.
split. unfold not; intros; contradiction.
split. unfold not; intros; contradiction.
unfold not; intros. inversion H8.
(*is b i l2a?*)
destruct (in_dec EV b l1a). apply split_list_In_first in i. destruct i as [l1a1 [l1a2 [? ?]]].
exists (a::l1a1). exists nil. exists b. exists (l1a2++v'::l1b). exists (v2::l2).
split. rewrite H1. subst l1a. simpl. rewrite app_comm_cons.
rewrite <- (app_assoc (a::l1a1) (b::l1a2)). simpl; auto.
split. simpl; auto.
split. unfold not; intros; contradiction.
split. unfold not; intros; contradiction.
unfold not; intros. inversion H8.
exists (a::l1a). exists (b::l2a). exists v'. exists l1b. exists l2b.
split. simpl. rewrite H1. auto.
split. simpl. rewrite H3. auto.
split. unfold not; intros.
destruct H6; destruct H7. subst a; subst b. contradiction.
subst a. contradiction. subst b. contradiction.
apply H4 in H6. contradiction.
split. unfold not; intros. destruct H6; destruct H7. subst a; subst b. contradiction.
subst b. contradiction. subst a. contradiction.
apply H5 in H7. contradiction. auto.
unfold not; intros. inversion H6. contradiction.
Qed.

Lemma first_point_of_divergence:
forall l1 l2 (u: V), hd_error l1 = Some u -> hd_error l2 = Some u -> l1 <> l2 ->
  exists la v l1b l2b, l1 = la++v::l1b /\ l2 = la++v::l2b /\ hd_error l1b <> hd_error l2b.
Proof.
induction l1; intros. inversion H.
destruct l2. inversion H0.
simpl in H. inversion H. subst a. simpl in H0. inversion H0. subst v. clear H H0.
destruct l1. destruct l2. contradiction.
exists nil. exists u. exists nil. exists (v::l2). simpl.
split. auto. split. auto. unfold not; intros; inversion H.
destruct l2. exists nil. exists u. exists (v::l1). exists nil. simpl.
split. auto. split. auto. unfold not; intros; inversion H.
rename v into a. rename v0 into b. destruct (EV a b).
++
hnf in e. subst b. assert (a::l1 <> a::l2). unfold not; intros; rewrite H in H1; contradiction.
apply (IHl1 (a::l2) a) in H; auto. destruct H as [la [x [l1b [l2b [? [? ?]]]]]].
exists (u::la). exists x. exists l1b. exists l2b.
simpl. split. rewrite H; auto. split. rewrite H0; auto. auto.
++
exists nil. exists u. exists (a::l1). exists (b::l2).
simpl. split. auto. split. auto. unfold complement, equiv in c. unfold not; intros. inversion H. contradiction.
Qed.

(*not strong enough... need to show l1b <> l2b too*)
Lemma first_divergence_bubble_ugly:
forall l1 l2 (u v: V), l1 <> l2 -> hd_error l1 = Some u -> hd_error l2 = Some u ->
  last_error l1 = Some v -> last_error l2 = Some v -> u <> v ->
  NoDup l1 -> NoDup l2 -> (*I'm sure this is unnecessary*)
  exists la x l1b l2b y l1c l2c,
    l1 = la++x::l1b++y::l1c /\ l2 = la++x::l2b++y::l2c /\
    (forall u, In u l1b -> ~ In u l2b) /\
    (forall u, In u l2b -> ~ In u l1b) /\ l1b <> l2b.
Proof.
intros. apply (first_point_of_divergence l1 l2 u) in H; auto.
destruct H as [la [x [l1b [l2b [? [? ?]]]]]]. subst l1; subst l2.
rewrite last_err_split2 in H2, H3.
destruct l1b. destruct l2b. contradiction. inversion H2. subst x.
rewrite last_error_cons in H3. apply last_error_In in H3.
apply NoDup_app_r in H6. apply NoDup_cons_2 in H6. contradiction.
unfold not; intros. inversion H.
destruct l2b. inversion H3. subst x. apply NoDup_app_r in H5. apply NoDup_cons_2 in H5.
rewrite last_error_cons in H2. apply last_error_In in H2. contradiction.
unfold not; intros. inversion H.
assert (In v (v1::l2b)). { rewrite last_error_cons in H3. apply last_error_In in H3. auto. unfold not; intros. inversion H. }
apply (first_point_of_convergence_ugly (v0::l1b) (v1::l2b) v) in H.
2: auto. 2: { rewrite last_error_cons in H2. apply last_error_In in H2. auto. unfold not; intros. inversion H7. }
destruct H as [l1b' [l2b' [y [l1c [l2c [? [? [? ?]]]]]]]].
rewrite H. rewrite H7.
exists la. exists x. exists l1b'. exists l2b'. exists y. exists l1c. exists l2c.
split. auto. split. auto. split; auto.
Qed.

Lemma uforest_uforest':
forall g, uforest g -> uforest' g.
Proof.
unfold uforest, uforest'; intros.
(*no self-loops*)
split. intros. apply uforest_no_self_loops; auto.
(*no multi-edges*)
split. intros. apply (uforest_no_multigraph g u v e1 e2); auto.
(*strong evalid*)
split. apply H.
(*unique_simple_upath*)
destruct H.
unfold unique_simple_upath; intros.
destruct (EV u v). hnf in e. subst v.
apply (simple_upath_self g u p1) in H1; auto. apply (simple_upath_self g u p2) in H3; auto.
rewrite H1, H3. auto.
unfold complement, equiv in c.
destruct (list_eqdec EV p1 p2). hnf in e; auto. unfold complement, equiv in c0. exfalso.
(*This is the tricky one. Need a lemma that finds the first "point" of divergence v1 and then the
first point of convergence v2 after that, so that the sublists p1' p2' connect v1 and v2, but
internal variables are all different.
   |--p1'--|
---x       y---
    \-p2'-/
Then the edges that fits_upath p1' and p2' cannot be identical as well
Then p1' ++ tl (rev p2') is a simple ucycle*)
assert (exists (la : list V) (x : V) (l1b l2b : list V) (y : V) (l1c l2c : list V),
       p1 = la ++ x :: l1b ++ y :: l1c /\
       p2 = la ++ x :: l2b ++ y :: l2c /\
       (forall u : V, In u l1b -> ~ In u l2b) /\ (forall u : V, In u l2b -> ~ In u l1b) /\ l1b <> l2b).
apply (first_divergence_bubble_ugly p1 p2 u v).
auto. apply H2. apply H4. apply H2. apply H4. auto. apply H1. apply H3.
destruct H5 as [pa [x [p1' [p2' [y [p1c [p2c ?]]]]]]]. destruct H5 as [? [? [? [? Hnot]]]].
subst p1. subst p2.
assert (connected_by_path g (x::p1'+::y) x y). {
split. replace (pa ++ x :: p1' ++ y :: p1c) with (pa++(x::p1'+::y)++p1c) in H2. destruct H2.
apply valid_upath_app_split in H2. destruct H2. apply valid_upath_app_split in H6. apply H6.
simpl. rewrite <- app_assoc. simpl. auto.
split. auto. rewrite app_comm_cons. apply last_err_appcons.
}
assert (simple_upath g (x::p1'+::y)). split. apply H5. destruct H1.
apply NoDup_app_r in H6. replace (x :: p1' ++ y :: p1c) with ((x::p1'+::y)++p1c) in H6.
apply NoDup_app_l in H6. auto.
simpl. rewrite <- app_assoc. simpl; auto.
assert (connected_by_path g (x::p2'+::y) x y). {
split. replace (pa ++ x :: p2' ++ y :: p2c) with (pa++(x::p2'+::y)++p2c) in H4. destruct H4.
apply valid_upath_app_split in H4. destruct H4. apply valid_upath_app_split in H10. apply H10.
simpl. rewrite <- app_assoc. simpl. auto.
split. auto. rewrite app_comm_cons. apply last_err_appcons.
}
assert (simple_upath g (x::p2'+::y)). split. apply H9. destruct H3.
apply NoDup_app_r in H10. replace (x :: p2' ++ y :: p2c) with ((x::p2'+::y)++p2c) in H10.
apply NoDup_app_l in H10. auto.
simpl. rewrite <- app_assoc. simpl; auto.
clear c0. clear H2 H1 H4 H3. clear p1c p2c pa. clear c u v.
replace (x :: p2' +:: y) with (rev ((y::(rev p2')+::x))) in *.
2: { simpl. rewrite rev_unit, rev_involutive. simpl; auto. }
apply connected_by_path_rev in H9. rewrite rev_involutive in H9.
apply simple_upath_rev in H10. rewrite rev_involutive in H10.
set (p:=(x::p1'+::y)++ tl (y::rev p2'+::x)).
assert (connected_by_path g p x x). unfold p.
apply (connected_by_path_join g _ _ x y x); auto.
assert (exists l, fits_upath g l p). apply connected_exists_list_edges in H1; auto.
destruct H2 as [l ?].
assert (simple_upath g (tl p)). {
  split. apply valid_upath_tail. apply H1.
unfold p. simpl.
apply NoDup_app_inv. destruct H6. apply NoDup_cons_1 in H4. auto.
destruct H10. apply NoDup_cons_1 in H4. auto.
unfold not; intros. apply in_app_or in H3; apply in_app_or in H4.
destruct H3; destruct H4.
rewrite <- in_rev in H4. apply H8 in H4. auto.
destruct H4. subst x0. destruct H6. apply NoDup_cons_2 in H6. apply H6.
apply in_or_app; left; auto. contradiction.
destruct H3. subst x0. destruct H10. apply NoDup_cons_2 in H10. apply H10.
apply in_or_app; left; auto. contradiction.
destruct H3; destruct H4; try contradiction. subst x0.
destruct H6. apply NoDup_cons_2 in H6. apply H6.
subst y. apply in_or_app. right; left; auto.
}
apply (H0 p l). unfold p, simple_ucycle, ucycle. split. apply H3.
simpl. destruct (p1' +:: y ++ rev p2' +:: x) eqn:Htmp.
assert (In x (p1' +:: y ++ rev p2' +:: x)). apply in_or_app; right; apply in_or_app; right; left; auto.
rewrite Htmp in H4; contradiction.
unfold p in H2. simpl in H2. rewrite Htmp in H2. destruct l. contradiction.
split. rewrite <- Htmp. apply H1. split. auto.
apply NoDup_cons.
--(*want to show that if it were, there would be two x or two v in l0*)
assert (Htl: connected_by_path g (tl p) v x). split. apply H3. split.
unfold p; simpl; rewrite Htmp; auto.
simpl. rewrite app_assoc. apply last_err_appcons.
simpl in Htl. rewrite Htmp in Htl.
unfold not; intros. destruct H2. unfold p in H3. simpl in H3. rewrite Htmp in H3. destruct H3.
assert (Hv: ~ In v l0). apply NoDup_cons_2 in H12; auto.
destruct l. contradiction. destruct l0. simpl in H11; contradiction.
destruct H4.
subst e0. destruct H11. assert (v0 = x). { destruct H2. destruct H4.
destruct H13; destruct H13; destruct H14; destruct H14; rewrite H13 in H14; rewrite H15 in H16.
apply NoDup_cons_2 in H12. exfalso; apply H12. left. auto.
auto. auto.
exfalso; apply NoDup_cons_2 in H12; apply H12; left; auto.
}
subst v0. clear H4. destruct l0.
++
(*show this means p1' = p2'*)
destruct p1'. destruct p2'. contradiction.
simpl in Htmp. inversion Htmp. destruct (rev p2'). simpl in H14. inversion H14. simpl in H14. inversion H14.
pose proof (app_not_nil (l0+::v0) x). contradiction.
inversion Htmp. destruct p1'. inversion H14.
pose proof (app_not_nil (rev p2') x). contradiction.
simpl in H14. inversion H14. rewrite app_assoc in H16.
pose proof (app_not_nil (p1' +:: y ++ rev p2') x). contradiction.
++
assert (In x (v0::l0)). apply last_error_In. apply Htl.
apply NoDup_cons_1 in H12. apply NoDup_cons_2 in H12. contradiction.
++
destruct H11. apply NoDup_cons_2 in H12. exfalso; apply H12.
destruct H2. destruct H14; destruct H14.
apply (fits_upath_vertex_dst_In g (v0::l0)) in H4. rewrite H15 in H4; auto. auto.
apply (fits_upath_vertex_src_In g (v0::l0)) in H4. rewrite H14 in H4; auto. auto.
--
(*NoDup l*)
apply fits_upath_cons in H2. rewrite <- Htmp in H2.
apply (simple_upath_list_edges_NoDup g (tl p) l). auto.
unfold p; simpl; auto.
Qed.

(*so as long as the graph is strong_evalid, uforest and uforest' are equiv*)

(******************LABELED GRAPHS******************)

Local Coercion pg_lg: LabeledGraph >-> PreGraph.
Local Coercion lg_gg: GeneralGraph >-> LabeledGraph. 

Context {DV DE DG: Type}.
Local Notation LGraph := (LabeledGraph V E DV DE DG).

Lemma is_partial_graph_adj_edge:
  forall (g1 g2: PGraph) e u v, is_partial_graph g1 g2 -> adj_edge g1 e u v -> adj_edge g2 e u v.
Proof.
intros. destruct H0. destruct H0. destruct H2.
destruct H. destruct H4. destruct H5.
split. split. apply H4; auto.
rewrite <- H5; auto. rewrite <- H6; auto.
rewrite <- H5; auto. rewrite <- H6; auto.
Qed.

Corollary is_partial_graph_adjacent:
  forall (g1 g2: PGraph) u v, is_partial_graph g1 g2 -> adjacent g1 u v -> adjacent g2 u v.
Proof.
intros. destruct H0 as [e ?]. exists e. apply (is_partial_graph_adj_edge g1); auto.
Qed.

Corollary is_partial_lgraph_adjacent:
  forall (g1 g2: LGraph) u v, is_partial_lgraph g1 g2 -> adjacent g1 u v -> adjacent g2 u v.
Proof.
intros. apply (is_partial_graph_adjacent g1). apply H. auto.
Qed.

Lemma is_partial_lgraph_valid_upath:
  forall (g1 g2: LGraph) p, is_partial_lgraph g1 g2 -> valid_upath g1 p -> valid_upath g2 p.
Proof.
intros. induction p. auto. destruct p. simpl. simpl in H0. apply H. apply H0.
destruct H0. split. apply (is_partial_lgraph_adjacent g1 g2); auto. auto.
Qed.

Lemma is_partial_lgraph_connected:
  forall (g1 g2: LGraph), is_partial_lgraph g1 g2 ->
    forall u v, connected g1 u v -> connected g2 u v.
Proof.
intros. destruct H0 as [p ?]. destruct H0.
exists p. split.
apply (is_partial_lgraph_valid_upath g1 g2); auto. auto.
Qed.

Definition labeled_spanning_uforest (t g: LGraph) :=
  spanning_uforest t g /\
  preserve_vlabel t g /\ preserve_elabel t g.

(****************FINITE GRAPHS*****************)

Lemma path_partition_checkpoint':
forall (g: PGraph) {fg: FiniteGraph g} (l1 l2: list V) p l a b, Permutation (l1++l2) (VList g) ->
  In a l1 -> In b l2 -> connected_by_path g p a b -> fits_upath g l p ->
  exists v1 v2, In v1 p /\ In v2 p /\
    In v1 l1 /\ In v2 l2 /\ (exists e, adj_edge g e v1 v2 /\ In e l).
Proof.
  induction p; intros. destruct H2. destruct H4. inversion H4.
  destruct p. destruct H2. destruct H4. inversion H4; inversion H5; subst a. subst a0.
  assert (~ In b l2).
  apply (NoDup_app_not_in V l1). apply (Permutation_NoDup (l:=VList g)).
  apply Permutation_sym; auto. apply NoDup_VList. auto. contradiction.
  destruct l. simpl in H3; contradiction.
  destruct H2. destruct H4. destruct H2. inversion H4. subst a0.
  assert (In v (l1 ++ l2)). apply (Permutation_in (l:=VList g)). apply Permutation_sym; auto.
  rewrite VList_vvalid. apply adjacent_requires_vvalid in H2; apply H2.
  apply in_app_or in H7; destruct H7.
  assert (exists v1 v2 : V, In v1 (v :: p) /\ In v2 (v :: p) /\
    In v1 l1 /\ In v2 l2 /\ (exists e, adj_edge g e v1 v2 /\ In e l)). apply (IHp l v b); auto.
  split. auto. split. simpl; auto. rewrite last_error_cons in H5. auto.
    unfold not; intros. assert (In v (v::p)). left; auto. rewrite H8 in H9. contradiction. auto. apply H3.
  destruct H8 as [v1 [v2 [? [? [? [? ?]]]]]]. exists v1; exists v2. split. right; auto. split. right; auto.
  split; auto. split; auto. destruct H12 as [e0 [? ?]]. exists e0. split. auto. right; auto.
  exists a; exists v. split. left; auto. split. right; left; auto. split; auto. split; auto.
  destruct H3. exists e. split; auto. left; auto.
Qed.

Lemma path_partition_checkpoint:
forall (g: PGraph) {fg: FiniteGraph g} (l1 l2: list V) p a b, Permutation (l1++l2) (VList g) ->
  In a l1 -> In b l2 -> connected_by_path g p a b ->
  exists v1 v2, In v1 p /\ In v2 p /\
    In v1 l1 /\ In v2 l2 /\ adjacent g v1 v2.
Proof.
intros. assert (exists l, fits_upath g l p). apply connected_exists_list_edges in H2; auto. destruct H3 as [l ?].
pose proof (path_partition_checkpoint' g l1 l2 p l a b H H0 H1 H2 H3). destruct H4 as [v1 [v2 [? [? [? [? ?]]]]]].
exists v1; exists v2. repeat split; auto. destruct H8 as [e [? ?]]. exists e; auto.
Qed.

Definition DEList (g: LGraph) {fg: FiniteGraph g}: list DE :=
  map (elabel g) (EList g).

Definition sum_DE (DEadd: DE -> DE -> DE) (g: LGraph) {fg: FiniteGraph g} DEbase : DE :=
  fold_left DEadd (DEList g) DEbase.

(****************GRAPH ADD/REMOVE EDGES**************)

(*Only reasoning the cases when the added edge did not already exist*)
(*Tried to replace the adde_ versions with this in the main kruskal proof, but typing issues,
so not very helpful after all...*)
Lemma add_edge_adj_edge1:
forall (g: PGraph) e s d, vvalid g s -> vvalid g d -> adj_edge (pregraph_add_edge g e s d) e s d.
Proof.
unfold adj_edge; intros. split. apply add_edge_strong_evalid; auto.
rewrite add_edge_src. rewrite add_edge_dst. left; auto.
Qed.

Lemma add_edge_adj_edge2:
forall (g: PGraph) e s t e' u v,
  e <> e' -> (adj_edge g e' u v <-> adj_edge (pregraph_add_edge g e s t) e' u v).
Proof.
intros; split; intros.
+destruct H0. split.
apply add_edge_preserves_strong_evalid; auto.
rewrite add_edge_preserves_src; auto.
rewrite add_edge_preserves_dst; auto.
+destruct H0. apply add_edge_preserves_strong_evalid in H0; auto.
split. apply H0. rewrite add_edge_preserves_src, add_edge_preserves_dst in H1; auto.
Qed.

Lemma add_edge_valid_upath:
forall (g: PGraph) e s t p,
  ~ evalid g e -> valid_upath g p -> valid_upath (pregraph_add_edge g e s t) p.
Proof.
induction p; intros. auto.
destruct p. auto.
split. destruct H0. destruct H0. exists x.
apply add_edge_adj_edge2; auto. unfold not; intros; subst x.
destruct H0. destruct H0. contradiction.
apply IHp. auto. apply H0.
Qed.

Corollary add_edge_connected_by_path:
forall (g: PGraph) e s t p u v,
  ~ evalid g e -> connected_by_path g p u v -> connected_by_path (pregraph_add_edge g e s t) p u v.
Proof.
unfold connected_by_path; intros.
split. apply add_edge_valid_upath. auto.
apply H0. apply H0.
Qed.

Corollary add_edge_connected:
forall (g: PGraph) e s t u v,
  ~ evalid g e -> connected g u v -> connected (pregraph_add_edge g e s t) u v.
Proof.
intros. destruct H0 as [p ?]. exists p.
apply add_edge_connected_by_path; auto.
Qed.

Lemma add_edge_fits_upath:
forall (g: PGraph) e s t p l,
~ evalid g e -> fits_upath g l p -> fits_upath (pregraph_add_edge g e s t) l p.
Proof.
induction p; intros. destruct l; auto.
destruct l. auto. destruct p. auto.
split. destruct H0. destruct (EE e e0).
unfold equiv in e1; subst e0. destruct H0. destruct H0. contradiction.
unfold complement, equiv in c. apply add_edge_adj_edge2; auto.
apply IHp. apply H. apply fits_upath_cons in H0. apply H0.
Qed.

Lemma add_edge_fits_upath_rev:
forall (g: PGraph) e s d p l,
fits_upath (pregraph_add_edge g e s d) l p -> ~ In e l -> fits_upath g l p.
Proof.
induction p; intros. destruct l; auto.
destruct p. destruct l; auto.
destruct l. auto.
assert (Heq_e: e <> e0). unfold not; intros. apply H0. left; rewrite H1; auto.
assert (HIn_e: ~ In e l). unfold not; intros. apply H0. right; auto.
clear H0.
destruct H. split. destruct H. destruct H. split. split.
apply add_edge_evalid_rev in H; auto.
rewrite add_edge_preserves_src, add_edge_preserves_dst in H2; auto. simpl in H2; auto.
rewrite add_edge_preserves_src, add_edge_preserves_dst in H1; auto.
apply IHp; auto.
Qed.

Corollary add_edge_unaffected:
forall (g: PGraph) e s t p l, valid_upath (pregraph_add_edge g e s t) p
  -> fits_upath (pregraph_add_edge g e s t) l p -> ~ In e l -> valid_upath g p.
Proof.
intros. apply valid_upath_exists_list_edges'.
exists l. apply (add_edge_fits_upath_rev) in H0; auto.
Qed.

(*the following large lemmas are for proving uforest'*)
Lemma add_edge_connected_through_bridge1:
forall (g: PGraph) e u v a b, ~ evalid g e -> connected g a u -> connected g v b
  -> connected (pregraph_add_edge g e u v) a b.
Proof.
intros.
assert (vvalid g u). apply (connected_vvalid g a u H0).
assert (vvalid g v). apply (connected_vvalid g v b H1).
apply (add_edge_connected g e u v) in H0; auto. apply (add_edge_connected g e u v) in H1; auto.
destruct H0 as [x [? [? ?]]]. destruct H1 as [x0 [? [? ?]]].
exists (x++x0). split.
apply valid_upath_app; auto.
rewrite H5; rewrite H6. unfold adjacent_err. exists e. split.
apply (add_edge_strong_evalid g e u v); auto.
left. split. rewrite add_edge_src; auto. rewrite add_edge_dst; auto.
split. apply hd_error_app; auto. apply last_err_app; auto.
Qed.

Lemma add_edge_connected_through_bridge2:
forall (g: PGraph) e u v a b,
~ evalid g e -> connected g a v -> connected g u b -> connected (pregraph_add_edge g e u v) a b.
Proof.
intros.
assert (vvalid g v). apply (connected_vvalid g a v H0).
assert (vvalid g u). apply (connected_vvalid g u b H1).
apply (add_edge_connected g e u v) in H0; auto. apply (add_edge_connected g e u v) in H1; auto.
destruct H0 as [x [? [? ?]]]. destruct H1 as [x0 [? [? ?]]].
exists (x++x0). split.
apply valid_upath_app; auto.
rewrite H5; rewrite H6. unfold adjacent_err. exists e. split.
apply (add_edge_strong_evalid g e u v); auto.
right. split. rewrite add_edge_src; auto. rewrite add_edge_dst; auto.
split. apply hd_error_app; auto. apply last_err_app; auto.
Qed.

Lemma cross_bridge_implies_endpoints:
forall (g: PGraph) e u v p l a b,
~ connected g u v ->
simple_upath (pregraph_add_edge g e u v) p ->
connected_by_path (pregraph_add_edge g e u v) p a b ->
fits_upath (pregraph_add_edge g e u v) l p -> In e l ->
((connected g a u /\ connected g v b) \/ (connected g a v /\ connected g u b)).
Proof.
induction p; intros. destruct H1. destruct H4. inversion H4.
assert (a = a0). destruct H1. destruct H4. inversion H4. auto. subst a0. (*that was weird*)
destruct l. contradiction.
destruct p. contradiction.
(*so we show that v0 is connected to one of them. By trans, a0 is connected to one*)
(*case where (u,v) is first in list. Then we show a = u or a = v*)
destruct H3. subst e0.
destruct H2. destruct H2. destruct H2.
rewrite add_edge_src in H5, H4. rewrite add_edge_dst in H5, H4.
destruct H5. simpl in H5, H6.
assert (~ In e l). unfold not; intros.
  destruct H4; destruct H4; subst a; subst v0; destruct H0.
  assert (In u (v::p)). replace u with (src (pregraph_add_edge g e u v) e).
  apply (fits_upath_vertex_src_In _ (v::p) l e); auto.
  rewrite add_edge_src. auto. apply NoDup_cons_2 in H4. contradiction.
  assert (In v (u::p)). replace v with (dst (pregraph_add_edge g e u v) e).
  apply (fits_upath_vertex_dst_In _ (u::p) l e); auto.
  rewrite add_edge_dst. auto. apply NoDup_cons_2 in H4. contradiction.
destruct H4; destruct H4; subst a; subst v0.
left. split. apply connected_refl. auto. exists (v::p).
split. apply valid_upath_exists_list_edges'. exists l. apply (add_edge_fits_upath_rev g e u v). auto. auto.
split. simpl; auto. destruct H1. destruct H4. rewrite last_error_cons in H8; auto.
unfold not; intros; inversion H9.
right. split. apply connected_refl. auto. exists (u::p).
split. apply valid_upath_exists_list_edges'. exists l. apply (add_edge_fits_upath_rev g e u v). auto. auto.
split. simpl; auto. destruct H1. destruct H4. rewrite last_error_cons in H8; auto.
unfold not; intros; inversion H9.
(*Case where (u-v) is somewhere in the middle*)
assert (Hav0: connected g a v0). {
  apply adjacent_connected. destruct H2. destruct H2.
  assert (e <> e0). unfold not; intros. subst e0.
    rewrite add_edge_src in H5; rewrite add_edge_dst in H5.
    destruct H5; destruct H5; subst a; subst v0.
    assert (In u (v::p)). replace u with (src (pregraph_add_edge g e u v) e).
    apply (fits_upath_vertex_src_In _ (v::p) l e); auto.
    rewrite add_edge_src. auto.
    destruct H0. apply NoDup_cons_2 in H6. contradiction.
    assert (In v (u::p)). replace v with (dst (pregraph_add_edge g e u v) e).
    apply (fits_upath_vertex_dst_In _ (u::p) l e); auto.
    rewrite add_edge_dst. auto.
    destruct H0. apply NoDup_cons_2 in H6. contradiction.
  exists e0. destruct H2. repeat rewrite <- adde_vvalid in H7.
  rewrite add_edge_preserves_src in H5, H7; auto. rewrite add_edge_preserves_dst in H5, H7; auto.
  apply add_edge_evalid_rev in H2; auto.
  split; auto. split; auto.
}
(*IHp on v0*)
assert (connected g v0 u /\ connected g v b \/ connected g v0 v /\ connected g u b).
apply (IHp l v0 b). auto. split. apply H0.
destruct H0. apply NoDup_cons_1 in H4. auto.
destruct H1. destruct H4. split. apply H0.
split. simpl; auto. rewrite last_error_cons in H5; auto. unfold not; intros; inversion H6.
apply H2. apply H3.
destruct H4; destruct H4. left. split.
apply (connected_trans g a v0 u); auto. auto.
right. split.
apply (connected_trans g a v0 v); auto. auto.
Qed.

Lemma add_edge_bridge_split1:
forall (g: PGraph) e' u v p a b,
connected g u a ->
connected g v b ->
~ connected g u v ->
simple_upath (pregraph_add_edge g e' u v) p ->
(exists l, fits_upath (pregraph_add_edge g e' u v) l p /\ In e' l) ->
connected_by_path (pregraph_add_edge g e' u v) p a b
-> (exists p1 p2, p = p1++p2 /\
    connected_by_path g p1 a u /\
    connected_by_path g p2 v b).
Proof.
induction p; intros.
destruct H4. destruct H5. inversion H6.
destruct H3 as [l [? ?]].
destruct l. simpl in H5. contradiction.
destruct p. simpl in H3. contradiction.
assert (Hvvalid_g_u: vvalid g u). apply (connected_vvalid g u a0). auto.
assert (Hvvalid_g_v: vvalid g v). apply (connected_vvalid g v b). auto.
assert (a0 = a). destruct H4. destruct H6. simpl in H6. inversion H6. auto. subst a0.
destruct H5.
(*case where u-v is directly at the front*)
subst e. destruct H3. destruct H3.
rewrite add_edge_src in H6. rewrite add_edge_dst in H6.
destruct H6; destruct H6. subst a; subst v0. exists (u::nil); exists (v::p).
split. auto. split. split; simpl; auto.
assert (~ In e' l). unfold not; intros.
assert (In (src (pregraph_add_edge g e' u v) e') (v :: p)).
apply (fits_upath_vertex_src_In (pregraph_add_edge g e' u v) (v::p) l e'); auto.
rewrite add_edge_src in H7.
destruct H2. apply NoDup_cons_2 in H8. simpl in H8. contradiction.
split. apply valid_upath_exists_list_edges'. exists l. apply add_edge_fits_upath_rev in H5; auto.
split. simpl; auto. destruct H4. destruct H7. rewrite last_error_cons in H8. rewrite <- H8. auto.
unfold not; intros. simpl in H9. inversion H9.
subst a. contradiction.
(*otherwise*)
assert (e <> e'). unfold not; intros. subst e. destruct H3. destruct H3.
  rewrite add_edge_src in H7; rewrite add_edge_dst in H7.
  destruct H7; destruct H7; subst a; subst v0.
  assert (In (src (pregraph_add_edge g e' u v) e') (v :: p)).
  apply (fits_upath_vertex_src_In (pregraph_add_edge g e' u v) (v::p) l e'); auto.
  rewrite add_edge_src in H7. simpl in H7.
  destruct H2. apply NoDup_cons_2 in H8. simpl in H8. contradiction.
  assert (In (dst (pregraph_add_edge g e' u v) e') (u :: p)).
  apply (fits_upath_vertex_dst_In (pregraph_add_edge g e' u v) (u::p) l e'); auto.
  rewrite add_edge_dst in H7. simpl in H7.
  destruct H2. apply NoDup_cons_2 in H8. simpl in H8. contradiction.
assert (Hav0: adjacent g a v0). exists e. destruct H3. destruct H3.
  split. apply (add_edge_preserves_strong_evalid g e' u v e). auto. auto.
  rewrite add_edge_preserves_src in H8; auto. rewrite add_edge_preserves_dst in H8; auto.
assert (exists p1 p2,
        v0 :: p = p1++ p2 /\
        connected_by_path g p1 v0 u /\
        connected_by_path g p2 v b). apply (IHp v0 b); auto. (*<-------- WOW. If I use "apply IHp" instead of "apply (IHp v0 b)", universe inconsistency*)
apply (connected_trans g u a v0). auto.
apply adjacent_connected. auto.
destruct H2. split. apply H2. apply NoDup_cons_1 in H7. auto.
exists l. split. destruct H3. apply H7. apply H5.
destruct H4. destruct H4. split. apply H8.
destruct H7. rewrite last_error_cons in H9. auto. unfold not; intros. inversion H10.
(*WHEW*)
destruct H7 as [p1 [p2 [? [? ?]]]].
exists (a::p1). exists p2. split. rewrite H7. simpl; auto. split.
destruct H8. split. apply valid_upath_cons. apply H8.
destruct H10. rewrite H10. simpl. auto.
split. simpl; auto.
rewrite last_error_cons. apply H10.
destruct H10. unfold not; intros. subst p1. inversion H10.
auto.
Qed.

Lemma add_edge_bridge_split2:
forall (g: PGraph) e' u v p a b ,
connected g v a ->
connected g u b ->
~ connected g u v ->
simple_upath (pregraph_add_edge g e' u v) p ->
(exists l, fits_upath (pregraph_add_edge g e' u v) l p /\ In e' l) ->
connected_by_path (pregraph_add_edge g e' u v) p a b
-> (exists p1 p2, p = p1++p2 /\
    connected_by_path g p1 a v /\
    connected_by_path g p2 u b).
Proof.
induction p; intros.
destruct H4. destruct H5. inversion H6.
destruct H3 as [l ?]. destruct H3.
destruct l. simpl in *. contradiction.
destruct p. simpl in H3. contradiction.
assert (Hvvalid_g_v: vvalid g v). apply (connected_vvalid g v a0). auto.
assert (Hvvalid_g_u: vvalid g u). apply (connected_vvalid g u b). auto.
assert (a0 = a). destruct H4. destruct H6. inversion H6. auto. subst a0.
destruct H5.
(*case where u-v is directly at the front*)
subst e. destruct H3. destruct H3.
rewrite add_edge_src in H6. rewrite add_edge_dst in H6.
destruct H6; destruct H6; subst a; subst v0. apply connected_symm in H. contradiction.
exists (v::nil); exists (u::p).
split. auto. split. split; simpl; auto.
assert (~ In e' l). unfold not; intros.
assert (In v (u::p)). replace v with (dst (pregraph_add_edge g e' u v) e').
apply (fits_upath_vertex_dst_In (pregraph_add_edge g e' u v) (u::p) l e').
auto. auto. rewrite add_edge_dst. auto.
destruct H2. apply NoDup_cons_2 in H8. contradiction.
split. apply valid_upath_exists_list_edges'. exists l. apply (add_edge_fits_upath_rev g e' u v); auto.
split. simpl; auto. destruct H4. destruct H7. rewrite last_error_cons in H8. auto.
unfold not; intros. inversion H9.
(*otherwise*)
assert (e <> e'). unfold not; intros. subst e. destruct H3. destruct H3.
  rewrite add_edge_src in H7; rewrite add_edge_dst in H7.
  destruct H7; destruct H7; subst a; subst v0.
  assert (In u (v::p)). replace u with (src (pregraph_add_edge g e' u v) e').
  apply (fits_upath_vertex_src_In (pregraph_add_edge g e' u v) (v::p) l e'). auto. auto.
  rewrite add_edge_src. auto.
  destruct H2. apply NoDup_cons_2 in H8. contradiction.
  assert (In v (u::p)). replace v with (dst (pregraph_add_edge g e' u v) e').
  apply (fits_upath_vertex_dst_In (pregraph_add_edge g e' u v) (u::p) l e'). auto. auto.
  rewrite add_edge_dst. auto.
  destruct H2. apply NoDup_cons_2 in H8. contradiction.
assert (Hav0: adjacent g a v0). exists e. destruct H3. destruct H3.
  split. apply (add_edge_preserves_strong_evalid g e' u v e). auto. auto.
  rewrite add_edge_preserves_src in H8; auto. rewrite add_edge_preserves_dst in H8; auto.
assert (exists p1 p2,
        v0 :: p = p1++ p2 /\
        connected_by_path g p1 v0 v /\
        connected_by_path g p2 u b). apply (IHp v0 b); auto.
apply (connected_trans g v a v0). auto. apply adjacent_connected. auto.
destruct H2. split. apply H2. apply NoDup_cons_1 in H7. auto.
exists l. split. destruct H3. apply H7. apply H5.
destruct H4. destruct H4. split. apply H8.
split. auto.
destruct H7. rewrite last_error_cons in H9. auto. unfold not; intros. inversion H10.
(*WHEW*)
destruct H7 as [p1 [p2 ?]]. destruct H7. destruct H8.
exists (a::p1). exists p2. split. rewrite H7. simpl. auto. split.
destruct H8. split. apply valid_upath_cons. apply H8.
destruct H10. rewrite H10. simpl. auto.
split. simpl; auto.
rewrite last_error_cons. apply H10.
destruct H10. unfold not; intros. subst p1. inversion H10.
auto.
Qed.

Lemma add_edge_unique_simple_upath:
forall (g: PGraph) e' u v, unique_simple_upath g -> ~ connected g u v ->
  unique_simple_upath (pregraph_add_edge g e' u v).
Proof.
(*the forest definition*)
unfold unique_simple_upath; intros. rename u0 into a; rename v0 into b.
assert (exists l : list E, fits_upath (pregraph_add_edge g e' u v) l p1).
apply connected_exists_list_edges in H2; auto.
assert (exists l : list E, fits_upath (pregraph_add_edge g e' u v) l p2).
apply connected_exists_list_edges in H4; auto.
destruct H5 as [l1 ?]. destruct H6 as [l2 ?].
destruct (in_dec EE e' l1); destruct (in_dec EE e' l2).

+ assert ((connected g a u /\ connected g v b) \/ (connected g a v /\ connected g u b)).
apply (cross_bridge_implies_endpoints g e' u v p1 l1 a b); auto.
destruct H7; destruct H7.
(*case a-u and v-b*)
  apply connected_symm in H7.
  assert (exists p1_a p1_b, (p1 = p1_a++p1_b /\
      connected_by_path g p1_a a u /\
      connected_by_path g p1_b v b)).
  apply (add_edge_bridge_split1 g e' u v p1 a b); auto. exists l1; split; auto.
  destruct H9 as [p1_a [p1_b ?]]. destruct H9. destruct H10.
  assert (exists p2_a p2_b, (p2 = p2_a++p2_b /\
      connected_by_path g p2_a a u /\
      connected_by_path g p2_b v b)).
  apply (add_edge_bridge_split1 g e' u v p2 a b); auto. exists l2; split; auto.
  destruct H12 as [p2_a [p2_b ?]]. destruct H12. destruct H13.
  rewrite H9 in H1; rewrite H12 in H3. destruct H1. destruct H3.
  assert (p1_a = p2_a). apply (H a u p1_a p2_a).
  split. apply H10. apply (NoDup_app_l _ _ _ H15). auto.
  split. apply H13. apply (NoDup_app_l _ _ _ H16). auto.
  assert (p1_b = p2_b). apply (H v b p1_b p2_b).
  split. apply H11. apply (NoDup_app_r _ _ _ H15). auto.
  split. apply H14. apply (NoDup_app_r _ _ _ H16). auto.
  rewrite H9; rewrite H12; rewrite H17; rewrite H18. auto.
(*case a-v and u-b...*)
apply connected_symm in H7.
  assert (exists p1_a p1_b, (p1 = p1_a++p1_b /\
      connected_by_path g p1_a a v /\
      connected_by_path g p1_b u b)).
  apply (add_edge_bridge_split2 g e' u v p1 a b); auto. exists l1; split; auto.
  destruct H9 as [p1_a [p1_b ?]]. destruct H9. destruct H10.
  assert (exists p2_a p2_b, (p2 = p2_a++p2_b /\
      connected_by_path g p2_a a v /\
      connected_by_path g p2_b u b)).
  apply (add_edge_bridge_split2 g e' u v p2 a b); auto. exists l2; split; auto.
  destruct H12 as [p2_a [p2_b ?]]. destruct H12. destruct H13.
  rewrite H9 in H1; rewrite H12 in H3. destruct H1. destruct H3.
  (*by H, we have p1_a = p2_a*)
  assert (p1_a = p2_a). apply (H a v p1_a p2_a).         (*<--------- same issue here, I used "H a v" and let it infer the paths: universe inconsistency*)
  split. apply H10. apply (NoDup_app_l _ _ _ H15). auto.
  split. apply H13. apply (NoDup_app_l _ _ _ H16). auto.
  assert (p1_b = p2_b). apply (H u b p1_b p2_b).
  split. apply H11. apply (NoDup_app_r _ _ _ H15). auto.
  split. apply H14. apply (NoDup_app_r _ _ _ H16). auto.
  (*thus, rewrite*)
  rewrite H9; rewrite H12; rewrite H17; rewrite H18. auto.

+ (*In e' l1, ~In e' l2*)
(* Then p1 = p1_a++p1_b. p1_a connects a-u, p1_b connects v-b
Whereas p2 is valid in g, connected a b
p1_a does not contain u-v by simpleness, so it is unaffected and valid in g
Ditto p1_b
Thus, connected g u a, connected g v b, connected g a b. Thus, connected g u v. Contra
Repeat for a-v,b-u...
*)
destruct H4. apply (add_edge_unaffected g e' u v p2 l2) in H4; auto.
assert (connected g a b). exists p2. split; auto.
assert ((connected g a u /\ connected g v b) \/ (connected g a v /\ connected g u b)).
apply (cross_bridge_implies_endpoints g e' u v p1 l1 a b); auto.
assert (connected g u v).
destruct H9; destruct H9.
  apply (connected_trans g u a v). apply connected_symm; auto.
  apply (connected_trans g a b v). auto. apply connected_symm; auto.
  apply (connected_trans g u b v). auto.
  apply (connected_trans g b a v). apply connected_symm; auto. auto.
contradiction.

+ (*~In e' l1, In e' l2*)
destruct H2. apply (add_edge_unaffected g e' u v p1 l1) in H2; auto.
assert (connected g a b). exists p1. split; auto.
assert ((connected g a u /\ connected g v b) \/ (connected g a v /\ connected g u b)).
apply (cross_bridge_implies_endpoints g e' u v p2 l2); auto.
assert (connected g u v).
destruct H9; destruct H9.
  apply (connected_trans g u a v). apply connected_symm; auto.
  apply (connected_trans g a b v). auto. apply connected_symm; auto.
  apply (connected_trans g u b v). auto.
  apply (connected_trans g b a v). apply connected_symm; auto. auto.
contradiction.

+ (*~In e' l1, ~In e' l2*)
(*then both p1 and p2 are valid in g*)
destruct H2. apply (add_edge_unaffected g e' u v p1 l1) in H2; auto.
destruct H4. apply (add_edge_unaffected g e' u v p2 l2) in H4; auto.
apply (H a b).
split. apply H2. apply H1. split; auto.
split. apply H4. apply H3. split; auto.
Qed.

Instance prod_EV: EqDec (V*V) eq.
Proof.
  hnf. intros [x] [y].
  destruct (equiv_dec x y).
  - hnf in e. destruct (EV v v0). hnf in e0. subst.
    + left; reflexivity.
    + right. intro. apply c. inversion H. reflexivity.
  - right; intro; apply c; inversion H; reflexivity.
Defined.

Lemma add_edge_unique_adj_edge:
forall (g: PGraph) e u v e', ~ connected g u v ->
  adj_edge (pregraph_add_edge g e u v) e' u v -> e' = e.
Proof.
intros. destruct H0. destruct H0.
destruct (EE e e'). auto. unfold complement, equiv in c.
exfalso. apply H. apply add_edge_evalid_rev in H0; auto.
rewrite add_edge_preserves_src, add_edge_preserves_dst in H2, H1; auto. simpl in H2.
apply adjacent_connected. exists e'. split. split; auto. auto.
Qed.

Lemma add_edge_uforest':
forall (g: PGraph) e' u v, uforest' g -> vvalid g u -> vvalid g v -> ~ connected g u v ->
  uforest' (pregraph_add_edge g e' u v).
Proof.
intros.
(*first assert u <> v, as they're not connected*)
assert (Huv: u<>v). unfold not; intros; subst u. pose proof (connected_refl g v H1). auto.
split.
(*no self loop*)
intros.
destruct (EE e e').
unfold Equivalence.equiv in e0. subst e.
rewrite add_edge_src, add_edge_dst; simpl; auto.
unfold RelationClasses.complement, Equivalence.equiv in c.
apply add_edge_evalid_rev in H3. 2: auto.
rewrite add_edge_preserves_src by auto. rewrite add_edge_preserves_dst by auto. apply H; auto.
(*not multigraph*)
split. intros. destruct H3.
(*destruct by cases: whether (u0,v0) = (u,v) or (v,u)*)
destruct (prod_EV (u0,v0) (u,v)). hnf in e; inversion e. subst u0; subst v0. clear e.
rewrite (add_edge_unique_adj_edge g e' u v e1); auto. rewrite (add_edge_unique_adj_edge g e' u v e2); auto.
destruct (prod_EV (u0,v0) (v,u)). hnf in e; inversion e. subst u0 v0. clear e c.
apply adj_edge_sym in H3. apply adj_edge_sym in H4.
rewrite (add_edge_unique_adj_edge g e' u v e1); auto. rewrite (add_edge_unique_adj_edge g e' u v e2); auto.
unfold complement, equiv in c, c0.
apply add_edge_adj_edge2 in H3. apply add_edge_adj_edge2 in H4. destruct H. destruct H5. apply (H5 u0 v0). split; auto.
unfold not; intros; subst e2. destruct H4. rewrite add_edge_src, add_edge_dst in H6. destruct H6; destruct H6; subst u0; subst v0; contradiction.
unfold not; intros; subst e1. destruct H3. rewrite add_edge_src, add_edge_dst in H6. destruct H6; destruct H6; subst u0; subst v0; contradiction.
(*evalid -> strong_evalid*)
split. intros.
destruct (EE e e').
unfold Equivalence.equiv in e0. subst e.
apply add_edge_strong_evalid; simpl; auto.
unfold RelationClasses.complement, Equivalence.equiv in c.
apply add_edge_preserves_strong_evalid. auto.
apply add_edge_evalid_rev in H3; auto. apply H. auto.
(*forest*)
apply add_edge_unique_simple_upath; auto. apply H.
Qed.

Lemma remove_edge_valid_upath:
forall (g: PGraph) e p l, valid_upath g p -> fits_upath g l p -> ~ In e l
  -> valid_upath (pregraph_remove_edge g e) p.
Proof.
intros. apply valid_upath_exists_list_edges'.
apply (fits_upath_transfer' _ _ _ (pregraph_remove_edge g e)) in H0. exists l; apply H0.
intros. simpl. split; auto.
intros. simpl. unfold removeValidFunc. split. apply (fits_upath_evalid g p l); auto.
unfold not; intros. subst e0. contradiction.
auto. auto.
Qed.

Lemma remove_edge_unaffected:
  forall (g: PGraph) e p, valid_upath (pregraph_remove_edge g e) p -> valid_upath g p.
Proof.
intros. pose proof (valid_upath_exists_list_edges _ p H). destruct H0 as [l ?].
apply valid_upath_exists_list_edges'.
apply (fits_upath_transfer' _ _ _ g) in H0. exists l; auto.
intros. split; auto.
intros. apply (fits_upath_evalid (pregraph_remove_edge g e) p l) in H1.
simpl in H1. unfold removeValidFunc in H1. apply H1. auto.
auto. auto.
Qed.

Lemma remove_edge_uforest':
  forall (g: PGraph) e, uforest' g -> evalid g e ->
    uforest' (pregraph_remove_edge g e) /\
    ~ connected (pregraph_remove_edge g e) (src g e) (dst g e).
Proof.
intros.
pose proof (remove_edge_evalid g e).
assert (Hvvalid: forall v1, vvalid (pregraph_remove_edge g e) v1 <-> vvalid g v1).
  intros. simpl. split; auto.
split.
{ split. intros. simpl. apply H. rewrite remove_edge_evalid in H2; apply H2.
split. intros. unfold adj_edge, strong_evalid in H2; simpl in H2. unfold removeValidFunc in H2. destruct H2. destruct H2. destruct H3.
  destruct H. destruct H6. apply (H6 u v e1 e2).
  split; split.
  split. apply H2. apply H2. apply H4.
  split. apply H3. apply H3. apply H5.
split. intros. rewrite remove_edge_evalid in H2; destruct H2.
destruct H. destruct H4. destruct H5.
apply remove_edge_preserves_strong_evalid; auto.
unfold unique_simple_upath; intros.
assert (exists l, fits_upath (pregraph_remove_edge g e) l p1). apply valid_upath_exists_list_edges. apply H2.
destruct H6 as [l1 ?].
assert (exists l, fits_upath (pregraph_remove_edge g e) l p2). apply valid_upath_exists_list_edges. apply H4.
destruct H7 as [l2 ?].
destruct (in_dec EE e l1).
apply (fits_upath_evalid (pregraph_remove_edge g e) p1) in i; auto.
rewrite remove_edge_evalid in i. destruct i. contradiction.
destruct (in_dec EE e l2).
apply (fits_upath_evalid (pregraph_remove_edge g e) p2) in i; auto.
rewrite remove_edge_evalid in i. destruct i. contradiction.
apply (fits_upath_transfer' p1 l1 _ g) in H6; auto.
apply (fits_upath_transfer' p2 l2 _ g) in H7; auto.
assert (valid_upath g p1). apply valid_upath_exists_list_edges'. exists l1. auto.
assert (valid_upath g p2). apply valid_upath_exists_list_edges'. exists l2. auto.
assert (unique_simple_upath g). apply H. unfold unique_simple_upath in H10.
destruct H2. destruct H4. destruct H3. destruct H5.
apply (H10 u v p1 p2). split; auto. split; auto. split; auto. split; auto.
intros. apply (fits_upath_evalid _ _ _ _ H7) in H8. apply H8.
intros. apply (fits_upath_evalid _ _ _ _ H6) in H8. apply H8.
}
{
unfold not, connected; intros.
destruct H2 as [p ?].
assert (exists l, fits_upath (pregraph_remove_edge g e) l p). apply valid_upath_exists_list_edges. apply H2.
destruct H3 as [l ?].
assert (fits_upath g l p). apply (fits_upath_transfer' p l (pregraph_remove_edge g e) g); auto.
intros. apply (fits_upath_evalid _ _ _ _ H3) in H4. apply H4.
assert (connected_by_path g p (src g e) (dst g e)). split.
apply valid_upath_exists_list_edges'. exists l; auto. destruct H2. auto.
assert (bridge g e (src g e) (dst g e)). apply (forest_adj_bridge g e (src g e) (dst g e) H).
apply strong_evalid_adj_edge. apply H. auto.
assert (In e l). unfold bridge in H6. apply (H6 p l); auto.
apply (fits_upath_evalid _ _ _ _ H3) in H7. rewrite remove_edge_evalid in H7. destruct H7. contradiction.
}
Qed.

End UNDIRECTED.
