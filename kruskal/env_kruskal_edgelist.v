Require Import VST.floyd.proofauto.
Require Import Coq.ZArith.ZArith.
Require Import RamifyCoq.floyd_ext.closed_lemmas.
Require Export RamifyCoq.kruskal.kruskal_edgelist.

Local Open Scope Z.

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.

Definition MAX_EDGES:= 8.
Definition t_struct_edge := Tstruct _edge noattr.
Definition t_wedgearray_graph := Tstruct _graph noattr.
Definition wedgerep := reptype t_struct_edge.
Instance wedgerep_inhabitant : Inhabitant wedgerep :=
                                    (Vundef, (Vundef, Vundef)).


(*Warning: reptype of a struct doesn’t destruct nicely*)
Definition def_wedgerep (x: reptype t_struct_edge) :=
  is_int I32 Signed (fst x) /\
  is_int I32 Signed (fst (snd x)) /\
  is_int I32 Signed (snd (snd x)).

(*Comparator*)
Definition wedge_le (x y: wedgerep) :=
match x, y with
| (Vint x',_),(Vint y',_) => Int.signed x' <= Int.signed y'
| _,_ => False
end.

Lemma wedge_le_refl: forall x, def_wedgerep x -> wedge_le x x.
Proof.
  intros. destruct H as [? [? ?]].
  unfold wedge_le. 
  rewrite (surjective_pairing x).
  destruct (fst x); trivial. lia.
Qed.

Definition wedge_eq (x y: wedgerep) :=
match x, y with
| (Vint x',_),(Vint y',_) => Int.signed x' = Int.signed y'
| _,_ => False
end.

Lemma wedge_eq_refl:
  forall x, def_wedgerep x -> wedge_eq x x.
Proof.
  intros. destruct H as [? [? ?]].
  unfold wedge_eq. rewrite (surjective_pairing x).
  destruct (fst x); trivial.
Qed.

Lemma wedge_eq_symm:
  forall x y, def_wedgerep x -> def_wedgerep y -> wedge_eq x y -> wedge_eq y x.
Proof.
  intros.
  destruct H as [? [? ?]].
  destruct H0 as [? [? ?]].
  rewrite (surjective_pairing x) in *.
  rewrite (surjective_pairing y) in *.
  unfold wedge_eq in *.
  destruct x, y; simpl fst in *; simpl snd in *.
  destruct y, y0; trivial. lia.
Qed.

Definition wedge_lt (x y: wedgerep) :=
match x, y with
| (Vint x',_),(Vint y',_) => Int.signed x' < Int.signed y'
| _,_ => False
end.

Lemma wedge_lt_irrefl:
   forall a, def_wedgerep a -> wedge_lt a a -> False.
Proof.
intros.
destruct H as [? [? ?]].
unfold wedge_lt in H0.
rewrite (surjective_pairing a) in *.
destruct (fst a); trivial. lia.
Qed.

Lemma wedge_lt_le:
  forall x y, def_wedgerep x -> def_wedgerep y -> wedge_lt x y -> wedge_le x y.
Proof.
intros.
destruct H as [? [? ?]].
destruct H0 as [? [? ?]].
unfold wedge_lt in H1.
unfold wedge_le.
rewrite (surjective_pairing x) in *.
rewrite (surjective_pairing y) in *.
destruct x, y.
simpl fst in *. simpl snd in *.
destruct y0, y; trivial. lia.
Qed.

Lemma wedge_lt_le_flip:
  forall x y, def_wedgerep x -> def_wedgerep y -> wedge_lt x y -> ~ (wedge_le y x).
Proof.
  unfold not; intros.
  destruct H as [? [? ?]].
  destruct H0 as [? [? ?]].
  unfold wedge_le in H2; unfold wedge_lt in H1.
  rewrite (surjective_pairing x) in *.
  rewrite (surjective_pairing y) in *.
  destruct x, y.
  simpl fst in *. simpl snd in *.
  destruct y0, y; trivial. lia.
Qed.

Lemma wedge_lt_eq_flip:
  forall x y, def_wedgerep x -> def_wedgerep y -> wedge_lt x y -> ~ (wedge_eq y x).
Proof.
  unfold not; intros.
  destruct H as [? [? ?]].
  destruct H0 as [? [? ?]].
  unfold wedge_eq in H2; unfold wedge_lt in H1.
  rewrite (surjective_pairing x) in *.
  rewrite (surjective_pairing y) in *.
  destruct x, y.
  simpl fst in *. simpl snd in *.
  destruct y0, y; trivial. lia.
Qed.

Lemma wedge_le_lt_flip:
  forall x y, def_wedgerep x -> def_wedgerep y -> wedge_le x y -> ~ (wedge_lt y x).
Proof.
  unfold not; intros.
  destruct H as [? [? ?]].
  destruct H0 as [? [? ?]].
  unfold wedge_lt in H2; unfold wedge_le in H1.
  rewrite (surjective_pairing x) in *.
  rewrite (surjective_pairing y) in *.
  destruct x, y.
  simpl fst in *. simpl snd in *.
  destruct y0, y; trivial. lia.
Qed.

Lemma wedge_eq_lt_flip:
  forall x y, def_wedgerep x -> def_wedgerep y -> wedge_eq x y -> ~ (wedge_lt y x).
Proof.
  unfold not; intros.
  destruct H as [? [? ?]].
  destruct H0 as [? [? ?]].
  unfold wedge_lt in H2; unfold wedge_eq in H1.
  rewrite (surjective_pairing x) in *.
  rewrite (surjective_pairing y) in *.
  destruct x, y.
  simpl fst in *. simpl snd in *.
  destruct y0, y; trivial. lia.
Qed.

Lemma is_wedge_middle:
  forall (before: list wedgerep) (bl: list wedgerep) (after: list wedgerep) i,
       Forall def_wedgerep bl ->
       Zlength before <= i < Zlength before + Zlength bl ->
       is_int I32 Signed (fst (Znth i (before ++ bl ++ after))) /\
       is_int I32 Signed (fst (snd (Znth i (before ++ bl ++ after)))) /\
       is_int I32 Signed (snd (snd (Znth i (before ++ bl ++ after)))).
Proof.
intros.
rewrite app_Znth2 by lia. rewrite app_Znth1 by lia.
eapply Forall_Znth; eauto. lia.
Qed.

