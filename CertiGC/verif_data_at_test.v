Require Import floyd.proofauto.
Require Import data_at_test.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Definition value := tuint.

Definition fiddle_spec :=
 DECLARE _fiddle
  WITH p: val, n: Z, tag: Z, contents: list Z
  PRE [ _p OF (tptr tuint) ]
          PROP  (Z.div tag 1024 = n)
          LOCAL (temp _p p)
          SEP (data_at Ews (tarray value (1+n)) 
                      (map Vint (map Int.repr (tag::contents)))
                      (offset_val (-sizeof value) p))
  POST [ tint ]
        PROP () LOCAL()
           SEP (TT).

Definition Gprog : funspecs := 
        ltac:(with_library prog [fiddle_spec]).

Lemma body_fiddle: semax_body Vprog Gprog f_fiddle fiddle_spec.
Proof.
start_function.
rename H into Htag.
assert_PROP (Zlength contents = n) as LEN. {
  entailer!.
  forget (tag/1024) as n.
  clear - H0.
  rewrite Zlength_cons in H0.
  rewrite !Zlength_map in H0.
  destruct (zlt n 0); [elimtype False | ].
  rewrite Z.max_l in H0 by omega.
  pose proof (Zlength_nonneg contents).
  omega.
  rewrite Z.max_r in H0 by omega. omega.  
}
assert (N0: 0 <= n)
  by (pose proof (Zlength_nonneg contents); omega).
(* STOP HERE. *)
assert_PROP (p = field_address0 (tarray value (1+n)) [ArraySubsc 1] (offset_val (-sizeof value) p)). {
  entailer!.
  unfold field_address0.
  rewrite if_true. simpl. rewrite offset_offset_val.
  destruct H as [H _].
  destruct p; try contradiction H. simpl. f_equal. rewrite Int.add_zero. auto.
  destruct H as [? [? [? [? [? [? [? ?]]]]]]].
  hnf. repeat simple apply conj; auto.
  split; hnf.
  auto. omega.
}
replace field_address0 with field_address in H by admit.
forward.
(*
Ltac call to "forward" failed.
Error:
Tactic failure: sc_new_instantiate should really not have failed (level 10).
*)

(** SPLITTING APPROACH **)

erewrite (split2_data_at_Tarray Ews value (1+n) 1 _ 
      (map Vint (map Int.repr (tag :: contents)))
      (map Vint (map Int.repr (tag :: nil)))
      (map Vint (map Int.repr (contents))));
  try omega; 
  try (autorewrite with sublist; apply JMeq_refl).
2: rewrite !sublist_map, sublist_1_cons;
   autorewrite with sublist; apply JMeq_refl.

assert_PROP (p = field_address (tarray value 1) [ArraySubsc 1] (offset_val (-sizeof value) p)). {
  entailer!.
  unfold field_address.
  rewrite if_true. simpl. rewrite offset_offset_val.
  destruct H as [H _].
  destruct p; try contradiction H. simpl. f_equal. rewrite Int.add_zero. auto.
  destruct H as [? [? [? [? [? [? [? ?]]]]]]].
  hnf. repeat simple apply conj; auto.
  split; hnf.
  auto. omega.
}

forward.
 
 2: omega.

  try reflexivity.


