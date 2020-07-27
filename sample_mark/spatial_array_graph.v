Require Import CertiGraph.msl_application.ArrayGraph.
Require Import VST.veric.SeparationLogic.
Require Import CertiGraph.unionfind.env_unionfind_arr.
Require Import CertiGraph.floyd_ext.share.

(*I suppose this focuses SpatialArrayGraphAssum to specifically the mpred type? Have no idea what it means*)
Instance SAGA_VST: SpatialArrayGraphAssum mpred. Proof. refine (Build_SpatialArrayGraphAssum _ _ _ _ _). Defined.

(* Translation of a rank-parent pair into the C representation *)
Definition vgamma2cdata (rpa : nat * Z) : reptype vertex_type :=
  match rpa with
  | (r, pa) => (Vint (Int.repr pa), Vint (Int.repr (Z.of_nat r)))
  end.

(*Some SpatialGraph wrap over the data_at mpred stated below?*)
Instance SAG_VST (sh: share): SpatialArrayGraph pointer_val mpred.
Proof.
(*       pointer_val         mpred *)
  exact (fun pt lst => data_at sh (tarray vertex_type (Z.of_nat (length lst)))
                               (map vgamma2cdata lst) (pointer_val_val pt)).
Defined.
