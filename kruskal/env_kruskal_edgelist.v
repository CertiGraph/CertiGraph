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
(* Eval compute in wedgerep. *)

(*yuck, but because destructing reptype t_struct_edge doesn't yield val*(val*val) *)
(*wedge_to_cdata should ensure def_wedgerep*)
Definition def_wedgerep (x: wedgerep) : Prop :=
exists w u v, x = (Vint w, (Vint u, Vint v)) /\ Int.min_signed <= Int.signed w <= Int.max_signed /\
                                 Int.min_signed <= Int.signed u <= Int.max_signed /\
                                 Int.min_signed <= Int.signed v <= Int.max_signed.

Definition wedge_le (x y: wedgerep) :=
match x, y with
| (Vint x',_),(Vint y',_) => Int.signed x' <= Int.signed y'
| _,_ => False
end.

Lemma wedge_le_refl: forall x, def_wedgerep x -> wedge_le x x.
Proof.
intros. destruct H. destruct H. destruct H. destruct H.
rewrite H; simpl. lia.
Qed.

Definition wedge_eq (x y: wedgerep) :=
match x, y with
| (Vint x',_),(Vint y',_) => Int.signed x' = Int.signed y'
| _,_ => False
end.

Lemma wedge_eq_refl:
  forall x, def_wedgerep x -> wedge_eq x x.
Proof.
intros.
destruct H; destruct H; destruct H; destruct H.
rewrite H. reflexivity.
Qed.

Lemma wedge_eq_symm:
  forall x y, def_wedgerep x -> def_wedgerep y -> wedge_eq x y -> wedge_eq y x.
Proof.
  intros.
  destruct H; destruct H; destruct H; destruct H. rewrite H in *.
  destruct H0; destruct H0; destruct H0; destruct H0. rewrite H0 in *.
  simpl in H1; simpl. lia.
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
destruct H; destruct H; destruct H; destruct H. rewrite H in H0. simpl in H0. lia.
Qed.

Lemma wedge_lt_le:
  forall x y, def_wedgerep x -> def_wedgerep y -> wedge_lt x y -> wedge_le x y.
Proof.
intros.
destruct H; destruct H; destruct H; destruct H. rewrite H in *.
destruct H0; destruct H0; destruct H0; destruct H0. rewrite H0 in *.
simpl in H1; simpl. lia.
Qed.

Lemma wedge_lt_le_flip:
  forall x y, def_wedgerep x -> def_wedgerep y -> wedge_lt x y -> ~ (wedge_le y x).
Proof.
unfold not; intros.
destruct H; destruct H; destruct H; destruct H. rewrite H in *.
destruct H0; destruct H0; destruct H0; destruct H0. rewrite H0 in *.
simpl in H1; simpl in H2. lia.
Qed.

Lemma wedge_lt_eq_flip:
  forall x y, def_wedgerep x -> def_wedgerep y -> wedge_lt x y -> ~ (wedge_eq y x).
Proof.
unfold not; intros.
destruct H; destruct H; destruct H; destruct H. rewrite H in *.
destruct H0; destruct H0; destruct H0; destruct H0. rewrite H0 in *.
simpl in H1; simpl in H2. lia.
Qed.

Lemma wedge_le_lt_flip:
  forall x y, def_wedgerep x -> def_wedgerep y -> wedge_le x y -> ~ (wedge_lt y x).
Proof.
unfold not; intros.
destruct H; destruct H; destruct H; destruct H. rewrite H in *.
destruct H0; destruct H0; destruct H0; destruct H0. rewrite H0 in *.
simpl in H1; simpl in H2; lia.
Qed.

Lemma wedge_eq_lt_flip:
  forall x y, def_wedgerep x -> def_wedgerep y -> wedge_eq x y -> ~ (wedge_lt y x).
Proof.
unfold not; intros.
destruct H; destruct H; destruct H; destruct H. rewrite H in *.
destruct H0; destruct H0; destruct H0; destruct H0. rewrite H0 in *.
simpl in H1; simpl in H2; lia.
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
eapply Forall_Znth; eauto.
eapply Forall_impl; try eassumption.
intros.
destruct H1; destruct H1; destruct H1; destruct H1. rewrite H1; simpl. auto.
lia.
Qed.

