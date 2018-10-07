Require Export VST.floyd.proofauto.

Parameter env_Graph : Type.
Definition V : Type := pointer_val.
Definition E : Type := V * nat.
Parameters src dst : env_Graph -> E -> V.
Parameter A : Type.

Parameter raw_field : Type.
Parameter max_fields : nat.
Parameter tagnum_ty : Type.
Parameter tagnum: Type.
Parameter fieldnum : Type.

Local Open Scope nat_scope.

Record LV : Type := {
  raw_mark : bool;
  raw_fields : list raw_field;
  raw_fieldsbound : 0 < List.length raw_fields < max_fields;
  raw_tag : tagnum_ty
}.
Definition LE : Type := unit.
 
Parameter vlabel : env_Graph -> V -> LV.
Parameter elabel : env_Graph -> E -> LE.
Parameter field: Type.

Definition maxfields_nat := Z.to_nat (two_power_nat 22).
Definition maxtags_nat := Z.to_nat (two_power_nat 8).

Record node_rep : Type :=
{
  nr_color : bool;
  nr_tag : tagnum;
  nr_fields: list field;
  nr_fields_bound : 0 < List.length nr_fields < maxfields_nat
}.

Local Close Scope nat_scope.

Record tagcode (A : Type) : Type := Build_tagcode
  { tag_bitsize : nat;
    tag_encode : A -> Z;
    tag_decode : Z -> A;
    tag_encode_range : forall a : A, 0 <= tag_encode a < two_power_nat tag_bitsize;
    tag_decode_encode : forall a : A, tag_decode (tag_encode a) = a
  }.

Parameter int_of_tag : (bool * tagnum * fieldnum) -> int.
Parameter nr2gctc : node_rep -> (bool * tagnum * fieldnum).
Parameter followEdge : env_Graph -> field -> val.

Definition value := tuint. (* this is going to prove inadequate soon *)

Parameter nodesize : node_rep -> Z.

Class PointwiseGraphPred (V E GV GE Pred: Type): Type := {
  vertex_at: V -> GV -> Pred;
  edge_at: E -> GE -> Pred
}.         

(* 
We would like the recursive...
Definition node_type (nr : node_rep) : type := 
  tarray (Tpointer node_type noattr) (nodesize nr).

Or even more correctly, we'd like...
Definition node_type (nr : node_rep) : type := 
  tarray (Tor (tuint) (Tpointer node_type noattr)) (nodesize nr).

But for now, we are settling for what is below.
*)
Definition node_type (nr : node_rep) : type := 
  tarray (Tpointer Tvoid noattr) (nodesize nr).

Program Definition node_pred (cs: compspecs) (sh: share) (g: env_Graph) (p: val) (nr : node_rep) : mpred :=
  @data_at
          cs
          sh
          (node_type nr)
          ((Vint (int_of_tag (nr2gctc nr))) ::
           (map (followEdge g) (nr_fields nr)))
          (offset_val (-sizeof value) p).

Instance SGP_VST  (cs: compspecs) (sh: share) (g: env_Graph) :
  PointwiseGraphPred val unit node_rep unit mpred.
refine (@Build_PointwiseGraphPred
          _ _ _ _ _
          (node_pred cs sh g) 
          (fun _ _ => emp)).
Defined.

