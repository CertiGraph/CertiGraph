(*Looted and modified from graph/path_lemmas.v
Idea is with a definition of connectedness, there's no need to explicitly define an undirected graph
Which sort of makes sense I guess, because every directed graph has an underlying undirected graph by just removing the direction
And directed graphs make more sense in C compared to ugraphs (correct me if I'm wrong)
*)

Require Import Coq.Logic.ProofIrrelevance.
(*Require Import RamifyCoq.lib.Coqlib.*)
Require Import RamifyCoq.lib.Ensembles_ext.
(*Require Import RamifyCoq.lib.EnumEnsembles.*)
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.graph_relation.
(*
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListDec.
*)

Section UNDIRECTED.

Context {V E: Type}.
Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.

Notation Gph := (PreGraph V E).

(*as long as there is an edge from u to v, u and v are connected, regardless of who is the src*)
Definition adj_edge (g: Gph) (e: E) (u v: V) :=
  strong_evalid g e /\ (*just evalid?*)
  ((src g e = u /\ dst g e = v) \/ (src g e = v /\ dst g e = u)).

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
Definition adj_edges g u v: Ensemble E := fun e => adj_edge g e u v.

(************CUSTOM LIST OPERATIONS************)
(*Since it makes sense for us to deal with l+::a a lot*)

(*curious this doesn't exist in the list library*)
Fixpoint last_error {A: Type} (l : list A): option A :=
match l with
| nil => None
| a::nil => Some a
| _::l' => last_error l'
end.

Lemma last_err_app:
  forall {A:Type} (l: list A) (a: A), last_error (l+::a) = Some a.
Proof.
induction l. auto. intros. rewrite <- app_comm_cons. rewrite <- (IHl a0). simpl.
destruct (l+::a0) eqn:H. assert (l+::a0 <> nil) by (apply app_not_nil). contradiction.
reflexivity.
Qed.

Lemma rev_hd_last:
  forall {A:Type} (l: list A), hd_error l = last_error (rev l).
Proof.
induction l. auto.
simpl. rewrite (last_err_app (rev l) a). reflexivity.
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

Lemma valid_upath_app:
  forall g p1 p2, valid_upath g p1 -> valid_upath g p2 -> adjacent_err g (last_error p1) (hd_error p2) -> valid_upath g (p1++p2).
Proof.
induction p1; intros.
-apply H0.
-destruct p1.
  +simpl. apply valid_upath_cons. apply H0. apply adjacent_err_hd. apply H1.
  +rewrite <- app_comm_cons. split. apply H. apply IHp1. apply H. apply H0. apply H1.
Qed.

Corollary valid_upath_concat:
  forall g p v, valid_upath g p -> adjacent_last g (last_error p) v -> valid_upath g (p+::v).
Proof.
intros. apply (valid_upath_app g p (v::nil)). apply H.
simpl. destruct (last_error p); simpl in H0. apply (adjacent_requires_vvalid g v0 v H0). apply H0.
destruct (last_error p); simpl in *; apply H0.
Qed.

Lemma valid_upath_rev:
  forall g p, valid_upath g p -> valid_upath g (rev p).
Proof.
induction p; intros. auto.
simpl. apply valid_upath_concat. apply IHp. apply (valid_upath_tail' g p a H).
rewrite <- rev_hd_last. destruct p. apply H.
simpl. destruct H. apply adjacent_symm. apply H.
Qed.

Definition upath_prop (P : Ensemble V)  (p: upath) : Prop :=
  Forall (fun v => P v) p.

Definition good_upath (g: Gph) (P : Ensemble V) : (upath -> Prop) := fun p => valid_upath g p /\ upath_prop P p.

Corollary good_upath_rev:
  forall g P p, good_upath g P p -> good_upath g P (rev p).
Proof.
intros. split. apply valid_upath_rev. apply H.
destruct H. unfold upath_prop in *; rewrite Forall_forall in *. intros. apply H0. rewrite In_rev; apply H1.
Qed.

Definition connected_by_path (g: Gph) (P : Ensemble V) (p: upath) (n : V) : Ensemble V :=
  fun n' => good_upath g P p /\ hd_error p = Some n /\ last_error p = Some n'.

Definition connected_by (g: Gph) (P : Ensemble V) (n : V) : Ensemble V :=
  fun n' => exists p, connected_by_path g P p n n'.

Definition connected (g: Gph) (n : V): Ensemble V:= connected_by g (fun _ => True) n.

Lemma connected_by_symm:
  forall g P u v, connected_by g P u v -> connected_by g P v u.
Proof.
unfold connected_by; unfold connected_by_path; intros.
destruct H. rename x into p. exists (rev p). split. apply good_upath_rev. apply H.
split. rewrite <- (rev_involutive p) in H. rewrite <- rev_hd_last in H. apply H.
rewrite rev_hd_last in H. apply H.
Qed.

Corollary connected_symm:
  forall g u v, connected g u v -> connected g v u.
Proof.
  intro; apply connected_by_symm.
Qed.

Definition connected_graph (g: Gph) := forall u v, vvalid g u -> vvalid g v -> connected g u v.

Definition simple_upath g p := valid_upath g p /\ NoDup p.
(*
Lemma paths_can_be_simplified:
  forall g p, valid_upath g p -> exists p', simple_upath g p' /\ simplified p p'
*)
(************(CONNECTED) COMPONENTS************)

Definition component (g: Gph) (P: Ensemble V):=
  forall u v, P u -> P u -> connected g u v. (*Here we only care about connectedness; and are using P as a set*)

Definition maximal_component (g: Gph) (P: Ensemble V):=
  component g P /\ forall u v, connected g u v -> P u -> P v.
(*
Lemma connected_graph_component:
  forall g P, connected_graph g -> maximal_component g P -> Same_set P (vvalid g).
*)
(************UNDIRECTED CYCLES************)

(*A valid upath is a ucycle if its start and end are the same*)
(*Exclude empty paths?*)
(*Alternative: If any element shows up twice?*)
Definition ucycle (p: upath) := hd_error p = last_error p /\ tail p <> nil.

Lemma ucycle_nil :
  forall p , p = nil -> ~ (ucycle p).
Proof.
unfold not; unfold ucycle; intros. destruct H0.
assert (tail p = nil). rewrite H. auto. contradiction.
Qed.

Lemma ucycle_single:
  forall u, ~ (ucycle (u::nil)).
Proof.
unfold not; unfold ucycle; intros. destruct H.
assert (tail (u::nil) = nil). auto. contradiction.
Qed.

(*This means that all ucycles must be. If self-loop, must be u->u*)

Definition simple_ucycle p := ucycle p /\ NoDup (tail p).

(*which is better?*)

Definition acyclic_ugraph g := forall p, simple_ucycle p -> ~ (valid_upath g p). (*so walking back and forth is an accepted "cycle", but we don't care*)

Definition acyclic_ugraph2 g := forall u v w, connected g u v -> connected g v w -> ~ (adjacent g u w).

(*A forest's more common definition is based on trees, but it's equivalent to an acyclic graph (requires proof)*)
Definition uforest g := acyclic_ugraph g.

Definition spanning_uforest g t := is_partial_graph t g /\ uforest t /\ (forall u v, connected g u v <-> connected t u v).

(*Next problem: graphs can be disconnected. So, the definition of a tree is dependent on components. E.g Prim's returns a tree of the component its root is in

Definition tree' g u :=
  forall v, connected_by g P u v -> (*only one path from u to v. Use NoDup?*).

Definition tree g :=
  forall u, tree' g u.
*)

End UNDIRECTED.