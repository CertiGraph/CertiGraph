Require Import FunctionalExtensionality.
Require Import List.
Require Import Omega.

Class EqDec (T: Type) := {t_eq_dec: forall t1 t2 : T, {t1 = t2} + {t1 <> t2}}.

Class Valid (T: Type) {EDT: EqDec T} := valid: T -> bool.

Definition sameValid (T : Type) (b: bool) {EDT: EqDec T} : Valid T := fun _ => b.

Definition modifyValid (T : Type) (t : T) (b : bool) {EDT: EqDec T} {V : Valid T} : Valid T :=
  fun (x : T) => if (t_eq_dec x t) then b else V x.

Class Pregraph (Vertex: Type) Edge Data {EV: EqDec Vertex} {VV : Valid Vertex}:=
  {
    node_label : Vertex -> Data;
    edge_source : Edge -> Vertex;
    edge_target : Edge -> Vertex
  }.

Class EdgeGraph (Vertex:Type) Edge Data {EV: EqDec Vertex} {VV: Valid Vertex} {PG : Pregraph Vertex Edge Data}:=
  {
    edge_func : Vertex -> list Vertex;
    consistency_1: forall e : Edge, In (edge_target e) (edge_func (edge_source e));
    consistency_2: forall v1 v2 : Vertex,
                     In v2 (edge_func v1) -> exists e : Edge, edge_source e = v1 /\ edge_target e = v2
  }.

Class BiGraph (Vertex: Type) Edge Data {EV: EqDec Vertex} {VV: Valid Vertex} {PG: Pregraph Vertex Edge Data} {EG: EdgeGraph Vertex Edge Data} :=
  {
    length_limit: forall v : Vertex, length (edge_func v) >= 2
  }.

Definition biEdge (Vertex : Type) Edge Data (v: Vertex) {EV: EqDec Vertex} {VV: Valid Vertex} {PG: Pregraph Vertex Edge Data} {EG: EdgeGraph Vertex Edge Data} {BG: BiGraph Vertex Edge Data} : Vertex * Vertex.
  specialize (length_limit v); intro Hlen;
  destruct (edge_func v); [simpl in Hlen; exfalso; intuition |
                           destruct l; [simpl in Hlen; exfalso; intuition | apply (v0, v1)]].
Defined.
