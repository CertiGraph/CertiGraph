(*Looted and modified from graph/path_lemmas.v
Idea is with a definition of connectedness, there's no need to explicitly define an undirected graph
Which sort of makes sense I guess, because every directed graph has an underlying undirected graph by just removing the direction
And directed graphs make more sense in C compared to ugraphs (correct me if I'm wrong)
*)
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListDec.
Require Import Coq.Logic.ProofIrrelevance.
Require Import RamifyCoq.lib.Ensembles_ext.
(*Require Import RamifyCoq.lib.Coqlib.*)
(*Require Import RamifyCoq.lib.EnumEnsembles.*)
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.graph_relation.
Require Import RamifyCoq.graph.path_lemmas.

Section UNDIRECTED.

Context {V E: Type}.
Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.

Notation Gph := (PreGraph V E).

(*as long as there is an edge from u to v, u and v are connected, regardless of who is the src*)
Definition adj_edge (g: Gph) (e: E) (u v: V) :=
  strong_evalid g e /\ (*just evalid?*)
  ((src g e = u /\ dst g e = v) \/ (src g e = v /\ dst g e = u)).

Lemma adj_edge_sym:
forall g e u v, adj_edge g e u v -> adj_edge g e v u.
Proof.
intros. destruct H. split; auto.
destruct H0. right; auto. left; auto.
Qed.

(*Consequently, we may not care about the exact nature of the edges*)
Definition adjacent (g: Gph) (u v: V) := exists e: E,
  adj_edge g e u v.

Lemma adjacent_requires_vvalid:
  forall g u v, adjacent g u v -> vvalid g u /\ vvalid g v.
Proof.
intros. destruct H. destruct H. destruct H0; destruct H0; rewrite <- H0; rewrite <- H1; split; apply H.
Qed.

Lemma adjacent_symm:
  forall g u v, adjacent g u v -> adjacent g v u.
Proof.
intros. destruct H. exists x. destruct H. destruct H0.
split. apply H. right. apply H0.
split. apply H. left. apply H0.
Qed.

(* But we may still need to pull out the edges, e.g. for labels
Problem is, because the graph is still fundamentally directed, there can be edges going a->b and b->a
So maybe we just return every such edge
But, it makes no sense having an undirected graph with more than one edge between two vertices
*)
Definition adj_edges g u v := fun e => adj_edge g e u v.

(************CUSTOM LIST OPERATIONS************)
(*Since it makes sense for us to deal with l+::a a lot*)

(*curious this doesn't exist in the list library*)
Fixpoint last_error {A: Type} (l : list A): option A :=
match l with
| nil => None
| a::nil => Some a
| _::l' => last_error l'
end.

Lemma last_error_cons: (*for convenience*)
  forall {A:Type} (l: list A) (a: A), l <> nil -> last_error (a::l) = last_error l.
Proof.
intros. destruct l. contradiction. simpl. reflexivity.
Qed.

Lemma last_err_appcons:
  forall {A:Type} (l: list A) (a: A), last_error (l+::a) = Some a.
Proof.
induction l. auto. intros. rewrite <- app_comm_cons. rewrite <- (IHl a0). simpl.
destruct (l+::a0) eqn:H. assert (l+::a0 <> nil) by (apply app_not_nil). contradiction.
reflexivity.
Qed.

Lemma last_err_app':
  forall {A:Type} (l2 l1: list A) (a: A), last_error l2 = Some a -> last_error (l1++l2) = Some a.
Proof.
induction l2; intros. inversion H.
destruct l2. simpl in H. inversion H. apply last_err_appcons.
assert (last_error (a::a1::l2) = last_error (a1::l2)). simpl. reflexivity. rewrite H0 in H.
assert (l1++a::a1::l2 = (l1+::a) ++ (a1::l2)).
assert (a:: a1 :: l2 = (a::nil)++a1::l2) by reflexivity. rewrite H1.
rewrite app_assoc. reflexivity. rewrite H1.
apply (IHl2 (l1+::a)). apply H.
Qed.

Lemma last_err_app:
  forall {A:Type} (l1 l2: list A) (a: A), last_error l2 = Some a -> last_error (l1++l2) = Some a.
Proof.
intros. apply (last_err_app' l2 l1 a H).
Qed.

Lemma last_err_split2:
forall {A: Type} (l1 l2: list A) (a: A),
last_error (l1++a::l2) = last_error (a::l2).
induction l1; intros. rewrite app_nil_l; auto.
replace (last_error ((a :: l1) ++ a0 :: l2)) with (last_error (l1 ++ a0 :: l2)).
2: { simpl. destruct (l1++a0::l2) eqn:Htmp.
  apply app_eq_nil in Htmp. destruct Htmp. inversion H0. auto. }
apply IHl1.
Qed.

Lemma hd_error_app:
  forall {A:Type} (l2 l1: list A) (a: A), hd_error l1 = Some a -> hd_error (l1++l2) = Some a.
Proof.
induction l1; intros. inversion H. simpl. simpl in H. auto.
Qed.

Lemma rev_hd_last:
  forall {A:Type} (l: list A), hd_error l = last_error (rev l).
Proof.
induction l. auto.
simpl. rewrite (last_err_appcons (rev l) a). reflexivity.
Qed.

Lemma hd_error_In:
  forall {A:Type} (l: list A) a, hd_error l = Some a -> In a l.
Proof.
intros. destruct l; simpl in H; inversion H. left; auto.
Qed.

Lemma last_error_In:
  forall {A:Type} (l: list A) a, last_error l = Some a -> In a l.
Proof.
induction l; intros. inversion H.
destruct l. inversion H. left; auto.
right. apply IHl. rewrite last_error_cons in H. apply H.
unfold not; intros. inversion H0.
Qed.

(*A bunch of helpers for convenience in handling options*)
Fixpoint adjacent_last g (u: option V) (v: V) :=
match u with
| None => vvalid g v
| Some u' => adjacent g u' v
end.

Fixpoint adjacent_hd g (u: V) (v: option V) :=
match v with
| None => vvalid g u
| Some v' => adjacent g u v'
end.

Fixpoint adjacent_err g (u: option V) (v: option V) :=
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

Fixpoint valid_upath (g: Gph) (p: upath) : Prop :=
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

Definition connected_by_path (g: Gph) (p: upath) (n : V) :=
  fun n' => valid_upath g p /\ hd_error p = Some n /\ last_error p = Some n'.

Definition connected (g: Gph) (n : V) :=
  fun n' => exists p, connected_by_path g p n n'.

Lemma connected_exists_path:
  forall (g: Gph) u v,
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

Definition connected_graph (g: Gph) := forall u v, vvalid g u -> vvalid g v -> connected g u v.

(************REASONING ABOUT A SPECIFIC LIST OF EDGES************)

Fixpoint fits_upath g (l: list E) (p: upath) :=
match l, p with
| nil, nil => True
| nil, v::nil => True
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
  forall g p, (forall v, In v p -> vvalid g v) -> (exists l, fits_upath g l p) -> valid_upath g p.
Proof.
induction p; intros. simpl. auto.
destruct p. simpl. apply H. left; auto.
destruct H0 as [l ?]. destruct l. simpl in H0; contradiction. destruct H0.
split. exists e; apply H0. apply IHp.
intros; apply H. right; apply H2.
exists l. apply H1.
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
simpl. auto.
simpl in H. destruct H. contradiction.
simpl in H. destruct H. contradiction.
simpl in H. destruct H. destruct H0. simpl. split; auto.
Qed.

Lemma fits_upath_evalid:
forall g p l, fits_upath g l p -> forall e, In e l -> evalid g e.
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

Corollary fits_upath_evalid':
forall g p l e, fits_upath g l p -> In e l -> evalid g e.
Proof.
intros. apply (fits_upath_evalid g p l) in H0; auto. Qed.

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

Lemma fits_upath_concat:
forall g p l e u, fits_upath g l p -> (exists v, last_error p = Some v /\ adj_edge g e u v) -> fits_upath g (l+::e) (p+::u).
Proof.
induction p; intros. destruct l. destruct H0 as [v [? ?]]. simpl in H0. inversion H0.
simpl in H. contradiction.
destruct p; destruct l. destruct H0 as [v [? ?]]. simpl in H0. inversion H0. subst a.
simpl. split; [apply adj_edge_sym; auto | auto].
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
split. simpl; auto. split; auto.
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
destruct H. exists nil. exists (e::nil). exists l. split; simpl; auto.
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

Lemma fits_upath_transfer':
forall p l g1 g2, (forall v, vvalid g1 v <-> vvalid g2 v) ->
(forall e, In e l -> evalid g2 e) -> (forall e, evalid g1 e -> evalid g2 e -> src g1 e = src g2 e) ->
(forall e, evalid g1 e -> evalid g2 e -> dst g1 e = dst g2 e) -> (*this is not quite what I want, hm*)
fits_upath g1 l p -> fits_upath g2 l p.
Proof.
induction p; intros. destruct l. auto. apply H3.
destruct l. destruct p. simpl. auto. simpl in H3. contradiction.
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
  forall g u v,
    adjacent g u v ->
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

Definition component (g: Gph) :=
  forall u v, connected g u v. (*Here we only care about connectedness; and are using as a set*)

Definition maximal_component (g: Gph):=
  component g /\ forall u v, connected g u v.
(*
Lemma connected_graph_component:
  forall g P, connected_graph g -> maximal_component g -> Same_set P (vvalid g).
*)

(************UFOREST************)

(*Use wiki/Bender & Williamson 2010's definition. Defining a cycle is troublesome because
1. have to deal with negations in definition of uforest
2. we support multiple edges btwn vertices, if so are they a cycle?
For the purposes of kruskal, we need uforest more than cycles*)

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

Lemma upath_simplifiable:
  forall g p u v, connected_by_path g p u v-> exists p', connected_by_path g p' u v /\ simple_upath g p' /\ incl p' p.
Proof.
induction p; intros.
destruct H. destruct H0. inversion H0.
destruct p. destruct H. simpl in H. simpl in H0; destruct H0.
inversion H0; inversion H1. subst u; subst v. clear H0 H1.
exists (a::nil). split. split. simpl; auto. simpl; split; auto.
split. split. simpl; auto. apply NoDup_cons. auto. apply NoDup_nil.
unfold incl; intros; auto.
destruct H. destruct H0. destruct H.
assert (connected_by_path g (v0::p) v0 v). split. auto. split. apply hd_error_cons. rewrite last_error_cons in H1; auto. unfold not; intros. inversion H3.
apply IHp in H3. destruct H3 as [p' ?]. destruct H3.
destruct (in_dec EV a p').
apply in_split in i. destruct i as [l1 [l2 ?]].
subst p'. exists (a::l2). split.
destruct H3. destruct H5. split. apply (valid_upath_app_split g l1 _).
apply H3. split. simpl in H0; simpl; apply H0.
rewrite last_err_split2 in H6. auto. destruct H4. split. apply simple_upath_app_split in H4; apply H4.
unfold incl; intros. destruct H6. subst a0. left; auto.
right. apply H5. apply in_or_app. right; right; apply H6.
exists (a::p'). split. destruct H3. destruct H5. split. apply valid_upath_cons. auto.
rewrite H5. unfold adjacent_hd. apply H.
split. simpl in H0; simpl; auto.
rewrite last_error_cons. auto. unfold not; intros. subst p'. inversion H5.
split. split. destruct H3. destruct H5. apply valid_upath_cons. auto. rewrite H5. unfold adjacent_hd. auto.
apply NoDup_cons. auto. apply H4.
unfold incl; intros. destruct H5. subst a0. left; auto. destruct H4. right; apply H6. auto.
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
intros. pose proof (upath_simplifiable g p u v H). destruct H0 as [p' [? [? ?]]].
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

(*barebones, this has a lot of loopholes*)
Definition uforest g :=
  (forall u v p1 p2,
  simple_upath g p1 -> connected_by_path g p1 u v ->
  simple_upath g p2 -> connected_by_path g p2 u v ->
  p1 = p2).

Definition sound_uforest g :=
  (forall e, evalid g e -> src g e <> dst g e) /\ (*No self-cycles*)
  (forall u v e1 e2, adj_edge g e1 u v /\ adj_edge g e2 u v -> e1 = e2) /\ (*Not a multigraph, preventing internal cycles within two vertices*)
  (forall e, evalid g e -> strong_evalid g e) /\ (*with no rubbish edges. Debatable where this should go?*)
  uforest g. (*finally, the actual forest definition*)

Lemma trivial_path1:
forall g e, strong_evalid g e -> connected_by_path g ((src g e)::(dst g e)::nil) (src g e) (dst g e) /\
fits_upath g (e::nil) ((src g e)::(dst g e)::nil).
Proof.
intros. split.
split. simpl. split. exists e. split. auto. left; auto. apply H.
simpl. auto.
simpl. split; auto. split. apply H. left; auto.
Qed.

(*Annnd even with the extra restrictions I STILL can't prove this
I'm going about this the wrong way. I need to convert p,l into a simple_upath p' l'
THEN I can use the fact that p' must be (u::v::nil) by uforest.
And because e::nil fits (u::v::nil), any lpath must be e::nil (prove this)
THEN e is in l', and by above we have incl l' l, thus e is in l
*)
Lemma forest_edge':
forall p l g e, sound_uforest g -> strong_evalid g e -> connected_by_path g p (src g e) (dst g e) ->
fits_upath g l p -> In e l.
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

(*to avoid having to keep destructing to find the uforest def*)
Lemma sound_uforest_uforest:
forall g, sound_uforest g -> uforest g.
Proof. intros. apply H. Qed.

Lemma sound_uforest_unique_lpath:
forall p l1 l2 g, sound_uforest g -> simple_upath g p -> fits_upath g l1 p -> fits_upath g l2 p -> l1 = l2.
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
forall p l g u v, sound_uforest g -> connected_by_path g p u v -> simple_upath g p -> fits_upath g l p ->
forall e, In e l -> bridge g e u v.
Proof.
induction p; intros.
destruct H0. destruct H4. inversion H4.
destruct p; destruct l. contradiction. simpl in H2. contradiction. simpl in H2. contradiction.
assert (a = u). destruct H0. destruct H4. inversion H4. auto. subst a.
unfold bridge; intros.
pose proof (upath_simplifiable_edges g p0 l0 u v H4 H5). destruct H6 as [p' [l' [? [? [? [? ?]]]]]]. apply H10.
assert (p' = (u::v0::p)). assert (uforest g). apply H. apply (H11 u v p' (u::v0::p)); auto. subst p'.
assert ((e0::l) = l'). apply (sound_uforest_unique_lpath (u::v0::p) (e0::l) l' g); auto. subst l'.
apply H3. (*hm, didn't need induction*)
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
unfold bridge in H0. assert (fits_upath g nil (a::nil)). simpl; auto. apply H0 in H1; auto. contradiction.
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
  sound_uforest t /\ (*it is also a forest*)
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

Lemma sound_uforest_no_simple_ucycles:
forall g, sound_uforest g -> (forall p l, valid_upath g p -> fits_upath g l p -> ~ simple_ucycle g p l).
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
Corollary sound_uforest_no_simple_ucycles':
forall g p l, sound_uforest g -> ~ simple_ucycle g p l.
Proof.
unfold not; intros. destruct H0.
destruct p. contradiction.
destruct p. contradiction.
destruct H1 as [? [? ?]]. destruct l. contradiction.
apply (sound_uforest_no_simple_ucycles g H (v::v0::p) (e::l)).
apply H1. auto. split. auto. split. auto. split. auto. auto.
Qed.

(*The proof of the converse will be finicky, because it requires reasoning about "do this"
But I don't think the converse is unnecessary;
At most, we redefine uforest in the no-cycle way and show that kruskal creates a tree that satisfies previous_def, thus is a uforest
*)
End UNDIRECTED.