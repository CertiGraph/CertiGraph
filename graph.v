Require Import FunctionalExtensionality.
Require Import List.
Require Import Omega.

Class EqDec (T: Type) := {t_eq_dec: forall t1 t2 : T, {t1 = t2} + {t1 <> t2}}.

Class Valid (T: Type) {EDT: EqDec T} := valid: T -> bool.

Definition sameValid (T : Type) (b: bool) {EDT: EqDec T} : Valid T := fun _ => b.

Definition modifyValid (T : Type) (t : T) (b : bool) {EDT: EqDec T} {V : Valid T} : Valid T :=
  fun (x : T) => if (t_eq_dec x t) then b else V x.

Class PreGraph (Vertex: Type) Data {EV: EqDec Vertex} {VV : Valid Vertex}:=
  {
    node_label : Vertex -> Data;
    edge_func : Vertex -> list Vertex
  }.

Class BiGraph (Vertex: Type) Data {EV: EqDec Vertex} {VV: Valid Vertex} {PG: PreGraph Vertex Data} :=
  {
    length_limit: forall v : Vertex, length (edge_func v) >= 2
  }.

Definition biEdge (Vertex : Type) Data (v: Vertex) {EV: EqDec Vertex} {VV: Valid Vertex} {PG: PreGraph Vertex Data} {BG: BiGraph Vertex Data} : Vertex * Vertex.
  specialize (length_limit v); intro Hlen;
  destruct (edge_func v); [simpl in Hlen; exfalso; intuition |
                           destruct l; [simpl in Hlen; exfalso; intuition | apply (v0, v1)]].
Defined.

Definition gamma (Vertex : Type) Data (v: Vertex) {EV: EqDec Vertex} {VV: Valid Vertex} {PG: PreGraph Vertex Data} {BG: BiGraph Vertex Data} : Data * Vertex * Vertex := let (v1, v2) := biEdge Vertex Data v in (node_label v, v1, v2).
