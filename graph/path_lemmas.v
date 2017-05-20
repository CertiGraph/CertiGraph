Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.omega.Omega.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.EnumEnsembles.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.find_not_in.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListDec.

Section PATH_LEM.

Context {V E: Type}.
Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.
Notation Gph := (PreGraph V E).

(******************************************

Definitions

******************************************)

Definition path : Type := (V * list E)%type.

Fixpoint valid_path' (g: Gph) (p: list E) : Prop :=
  match p with
    | nil => True
    | n :: nil => strong_evalid g n
    | n1 :: ((n2 :: _) as p') => strong_evalid g n1 /\ dst g n1 = src g n2 /\ valid_path' g p'
  end.

Definition valid_path (g: Gph) (p: path) :=
  match p with
  | (v, nil) => vvalid g v
  | (v, (e :: _) as p') => v = src g e /\ valid_path' g p'
  end.

Fixpoint epath_to_vpath' (g: Gph) (p : list E) {struct p} : list V :=
  match p with
  | nil => nil
  | e :: nil => src g e :: dst g e :: nil
  | e :: el => src g e :: epath_to_vpath' g el
  end.

Definition epath_to_vpath (g: Gph) (p: path) : list V :=
  match p with
  | (v, nil) => v :: nil
  | (_, p') => epath_to_vpath' g p'
  end.

Definition ptail (g: Gph) (p: path) : path :=
  match p with
  | (v, nil) => (v, nil)
  | (_, e :: el) => (dst g e, el)
  end.

Definition graph_is_acyclic (g: Gph) : Prop := forall p : path, valid_path g p -> NoDup (epath_to_vpath g p).

Definition path_prop' (g: Gph) (P : Ensemble V) : (list E -> Prop) := Forall (fun e => P (src g e) /\ P (dst g e)).

Definition path_prop (g: Gph) (P : Ensemble V)  (p: path) : Prop :=
  match p with
  | (v, nil) => P v
  | (_, p') => path_prop' g P p'
  end.

Definition good_path (g: Gph) (P : Ensemble V) : (path -> Prop) := fun p => valid_path g p /\ path_prop g P p.

Definition phead (p : path) : V := match p with | (v, _) => v end.

Fixpoint pfoot' (g: Gph) (l : list E) (v : V) : V :=
  match l with
  | nil => v
  | e :: nil => dst g e
  | _ :: l' => pfoot' g l' v
  end.

Definition pfoot (g: Gph) (p: path) : V := match p with (v, l) => pfoot' g l v end.

Definition path_endpoints (g: Gph) (p: path) (n1 n2 : V) : Prop := phead p = n1 /\ pfoot g p = n2.

Definition reachable_by_path (g: Gph) (p: path) (n : V) (P : Ensemble V) : Ensemble V :=
  fun n' => path_endpoints g p n n' /\ good_path g P p.
Notation " g '|=' p 'is' n1 '~o~>' n2 'satisfying' P" := (reachable_by_path g p n1 P n2) (at level 1).

Definition reachable_by (g: Gph) (n : V) (P : Ensemble V) : Ensemble V := fun n' => exists p, g |= p is n ~o~> n' satisfying P.
Notation " g '|=' n1 '~o~>' n2 'satisfying' P " := (reachable_by g n1 P n2) (at level 1).

Definition reachable_by_acyclic (g: Gph) (n : V) (P : Ensemble V) : Ensemble V :=
  fun n' => exists p, NoDup (epath_to_vpath g p) /\ g |= p is n ~o~> n' satisfying P.
Notation " g '|=' n1 '~~>' n2 'satisfying' P " := (reachable_by_acyclic g n1 P n2) (at level 1).

Definition reachable (g: Gph) (n : V): Ensemble V:= reachable_by g n (fun _ => True).

Definition reachable_by_through_set (g: Gph) (S : list V) (P : Ensemble V) : Ensemble V:= fun n => exists s, In s S /\ reachable_by g s P n.

Definition reachable_through_set (g: Gph) (S : list V) : Ensemble V:= fun n => exists s, In s S /\ reachable g s n.

Definition reachable_list (g: Gph) (x : V) (L : list V) : Prop := forall y, In y L <-> reachable g x y.

Definition reachable_set_list (g: Gph) (S : list V) (l : list V) : Prop := forall x : V, In x l <-> reachable_through_set g S x.

Definition is_tree (g : Gph) (x : V) : Prop := forall y, reachable g x y -> exists !(p : path), g |= p is x ~o~> y satisfying (fun _ => True).

Definition paths_meet_at (g: Gph) (p1 p2 : path) := fun n => pfoot g p1 = n /\ phead p2 = n.

Definition paths_meet (g: Gph) (p1 p2 : path) : Prop := exists n, paths_meet_at g p1 p2 n.

Definition In_path (g: Gph) (v: V) (p: path): Prop := v = fst p \/ exists e, In e (snd p) /\ (v = src g e \/ v = dst g e).

Definition Subpath (g: Gph) (p1 p2: path): Prop := incl (snd p1) (snd p2) /\ In_path g (fst p1) p2.

(******************************************

Path Lemmas
 
******************************************)

Lemma path_endpoints_meet: forall (g: Gph) p1 p2 n1 n2 n3,
  path_endpoints g p1 n1 n2 ->
  path_endpoints g p2 n2 n3 ->
  paths_meet g p1 p2.
Proof.
  unfold path_endpoints, paths_meet; intros.
  destruct H, H0. exists n2. split; tauto.
Qed.

Lemma pfoot_last: forall (g: Gph) p n s, pfoot g (s, p +:: n) = dst g n.
Proof.
  intros. induction p. 1: simpl; auto.
  rewrite <- app_comm_cons. simpl in *. destruct (p +:: n) eqn:? .
  + destruct p; inversion Heql.
  + auto.
Qed.

Lemma pfoot_head_irrel: forall l (g: Gph) v1 v2 n, pfoot g (v1, n :: l) = pfoot g (v2, n :: l).
Proof.
  induction l; intros; simpl; auto. specialize (IHl g v1 v2 a). simpl in *. apply IHl.
Qed.

Lemma paths_foot_head_meet: forall (g: Gph) p1 p2 n v s, dst g n = v -> paths_meet g (s, p1 +:: n) (v, p2).
Proof. intros. exists v. split. 2: simpl; auto. rewrite pfoot_last. auto. Qed.

Definition path_glue (p1 p2 : path) : path := (fst p1, (snd p1) ++ (snd p2)).
Notation "p1 '+++' p2" := (path_glue p1 p2) (at level 20, left associativity).

Lemma path_glue_nil_l: forall p v, (v, nil) +++ p = (v, snd p).
Proof.
  unfold path_glue.  trivial.
Qed.

Lemma path_glue_nil_r: forall p v, p +++ (v, nil) = p.
Proof.
  unfold path_glue. simpl. intros. rewrite app_nil_r. destruct p. trivial.
Qed.

Lemma path_glue_assoc: forall (g: Gph) (p1 p2 p3 : path),
  paths_meet g p1 p2 -> paths_meet g p2 p3 -> (p1 +++ p2) +++ p3 = p1 +++ (p2 +++ p3).
Proof.
  unfold path_glue. intros. destruct p1 as [v1 p1]. destruct p2 as [v2 p2].
  destruct p3 as [v3 p3]. simpl. rewrite <- app_assoc. auto.
Qed.

Lemma path_endpoints_glue: forall g n1 n2 n3 p1 p2,
  path_endpoints g p1 n1 n2 -> path_endpoints g p2 n2 n3 -> path_endpoints g (p1 +++ p2) n1 n3.
Proof.
  intros. destruct H, H0. split.
  icase p1. icase p2. icase p1. simpl in *. subst v0 v. destruct l; simpl.
  + rewrite app_nil_r. subst. auto.
  + clear H1. revert H2. induction l0; intros.
    - rewrite app_nil_l. pose proof (pfoot_head_irrel l g n1 n2 e). unfold pfoot in H.
      rewrite H. auto.
    - specialize (IHl0 H2). clear H2. rewrite <- app_comm_cons. simpl.
      remember (l0 ++ e :: l) as l'. destruct l'; auto. destruct l0; inversion Heql'.
Qed.

Lemma paths_meet_cons: forall g v e p1 p2, paths_meet g (v, e :: p1) p2 -> paths_meet g (dst g e, p1) p2.
Proof.
  intros. destruct H as [? [? ?]]. exists x. split; auto. simpl in H |-* . destruct p1. 1: simpl; auto.
  pose proof (pfoot_head_irrel p1 g v (dst g e) e0). unfold pfoot in H1. rewrite H in H1. auto.
Qed.

Lemma valid_path_cons: forall g v e p, valid_path g (v, e :: p) -> valid_path g (dst g e, p).
Proof.
  intros. destruct H. simpl in *. destruct p.
  + destruct H0 as [? [? ?]]. auto.
  + destruct H0; auto.
Qed.

Lemma valid_path_tail: forall g p, valid_path g p -> valid_path g (ptail g p).
Proof.
  intros. destruct p as [v p]. destruct p; unfold ptail; auto.
  apply valid_path_cons with v; auto.
Qed.

Lemma valid_path_split: forall g p1 p2, paths_meet g p1 p2 -> valid_path g (p1 +++ p2) -> valid_path g p1 /\ valid_path g p2.
Proof.
  intros g p1. destruct p1 as [v1 p1]. revert v1.
  induction p1; intros; destruct p2 as [v2 p2]; unfold path_glue, fst, snd in H0.
  + split.
    - simpl in H0 |-* . destruct p2; auto. destruct H0. subst. simpl in H1. destruct p2; [|destruct H1 as [H1 _]]; destruct H1 as [_ [H1 _]]; apply H1.
    - rewrite app_nil_l in H0. destruct H as [x [? ?]]. simpl in H, H1. subst v1. subst v2. auto.
  + specialize (IHp1 (dst g a) (v2, p2)). unfold path_glue, fst, snd in IHp1. rewrite <- app_comm_cons in H0.
    specialize (IHp1 (paths_meet_cons _ _ _ _ _ H) (valid_path_cons _ _ _ _ H0)). destruct IHp1. split; auto.
    clear H2 H. destruct H0. split; auto. simpl in *.  destruct p1. destruct (nil ++ p2); intuition. split; auto.
    destruct ((e :: p1) ++ p2); intuition.
Qed.

Lemma valid_path_app: forall g v p1 p2, valid_path g (v, p1 ++ p2) -> valid_path g (v, p1) /\ valid_path g (pfoot g (v, p1), p2).
Proof. intros. assert (paths_meet g (v, p1) (pfoot g (v, p1), p2)) by (exists (pfoot g (v, p1)); split; auto). apply valid_path_split; auto. Qed.

Lemma valid_path_merge: forall (g : Gph) p1 p2,
                          paths_meet g p1 p2 -> valid_path g p1 -> valid_path g p2 -> valid_path g (p1 +++ p2).
Proof.
  intros g p1. destruct p1 as [v1 p1]. revert v1.
  induction p1; intros; destruct p2 as [v p2]; unfold path_glue; unfold fst, snd.
  + destruct H as [v' [? ?]]. simpl in H, H2. rewrite <- H in H2. clear v' H.
    subst. rewrite app_nil_l. auto.
  + specialize (IHp1 (dst g a) (v, p2)). unfold path_glue, fst, snd in IHp1. specialize (IHp1 (paths_meet_cons _ _ _ _ _ H) (valid_path_cons _ _ _ _ H0) H1).
    rewrite <- app_comm_cons. destruct H0. red. split; auto.
    clear H1. simpl in *. destruct (p1 ++ p2) eqn:? .
    - destruct p1. auto. rewrite <- app_comm_cons in Heql. inversion Heql.
    - destruct p1; intuition.
Qed.

Lemma valid_path_si: forall (g1 g2: Gph),
    structurally_identical g1 g2 -> forall p, valid_path g1 p <-> valid_path g2 p.
Proof.
  cut (forall g1 g2 : Gph, g1 ~=~ g2 -> forall p : path, valid_path g1 p -> valid_path g2 p).
  1: intros; split; apply H; [| symmetry]; auto.
  intros. destruct p as [v p]. revert v H0. induction p; intros.
  + destruct H as [? _]. simpl in *. rewrite <- H. auto.
  + specialize (IHp (dst g1 a)). destruct H0. simpl in H1. split.
    - destruct H as [_ [? [? _]]]. destruct p; [| destruct H1 as [? _]]; destruct H1 as [? [? ?]]; specialize (H a); rewrite <- H2; intuition.
    - assert (strong_evalid g1 a -> strong_evalid g2 a). {
        intros. destruct H2 as [? [? ?]]. destruct H as [? [? [? ?]]]. assert (evalid g2 a) by (rewrite <- H5; auto).
        specialize (H6 _ H2 H8). specialize (H7 _ H2 H8). rewrite H6, H7 in *. rewrite H in H3, H4. split; auto.
      } destruct p. 1: simpl; apply H2; auto. destruct H1 as [? ?]. unfold valid_path in IHp. specialize (IHp H3).
      destruct H3, IHp. simpl. split. 1: apply H2; auto. split.
      * rewrite <- H5. symmetry. specialize (H2 H1). destruct H1, H2. destruct H as [_ [_ [_ ?]]]. apply H; auto.
      * apply H6.
Qed.

Lemma epath_to_vpath_cons: forall g v e p a l, epath_to_vpath g (v, e :: p) = a :: l -> epath_to_vpath g (dst g e, p) = l.
Proof. intros. simpl in *. destruct p; inversion H; auto. Qed.

Lemma epath_to_vpath_split: forall (g: Gph) n l1 l2 p, valid_path g p -> epath_to_vpath g p = l1 ++ (n :: l2) ->
                                                       exists p1 p2, p = p1 +++ p2 /\ valid_path g p1 /\ valid_path g p2 /\
                                                                     epath_to_vpath g p1 = l1 +:: n /\ epath_to_vpath g p2 = n :: l2.
Proof.
  intros g n. induction l1; intros.
  + rewrite app_nil_l in H0. exists (n, nil), p. simpl. split; [|split; [|split; [|split]]]; auto; destruct p as [v p].
    - unfold path_glue. simpl. simpl in H. destruct p. 1: inversion H0; auto. f_equal; auto. simpl in H0. destruct H. subst v. destruct p; inversion H0; auto.
    - simpl in H0, H. destruct p. 1: inversion H0; subst; auto. destruct H. simpl in H0, H1.
      destruct p; [|destruct H1 as [? _]]; destruct H1 as [_ [? _]]; inversion H0; subst; auto.
  + destruct p as [v p]. rewrite <- app_comm_cons in H0. destruct p. 1: simpl in H0; inversion H0; destruct l1; inversion H3.
    specialize (IHl1 l2 (dst g e, p) (valid_path_cons _ _ _ _ H) (epath_to_vpath_cons _ _ _ _ _ _ H0)). destruct IHl1 as [p1 [p2 [? [? [? [? ?]]]]]].
    exists (v, e :: (snd p1)), p2. split; [|split; [|split; [|split]]]; auto; destruct p1 as [v1 p1]; destruct p2 as [v2 p2]; unfold path_glue, fst, snd in *.
    - rewrite <- app_comm_cons. inversion H1. auto.
    - clear H4 H5 H0 H3. inversion H1. subst p. clear H1. destruct H. split; auto. simpl in *. destruct p1.
      * destruct (nil ++ p2); intuition.
      * rewrite <- H3 in H2. split; auto. destruct ((e0 :: p1) ++ p2); intuition.
    - rewrite <- app_comm_cons. inversion H1. subst p. clear H1 H3 H5. simpl epath_to_vpath in *. destruct p1.
      * rewrite <- H4. f_equal. destruct (nil ++ p2); inversion H0; auto. rewrite H7; auto.
      * rewrite H4. f_equal; auto. destruct ((e0 :: p1) ++ p2); inversion H0; auto.
Qed.

Lemma epath_to_vpath_pfoot: forall g p l a, epath_to_vpath g p = l +:: a -> pfoot g p = a.
Proof.
  intros g p. destruct p as [v p]; revert v. induction p; intros.
  + simpl in *. destruct l. rewrite app_nil_l in H. inversion H; auto. inversion H. destruct l; inversion H2.
  + simpl in H |-* . destruct p.
    - destruct l. rewrite app_nil_l in H. inversion H. destruct l.
      * simpl in H. inversion H. auto.
      * simpl in H. inversion H. destruct l; inversion H3.
    - destruct l. 1: rewrite app_nil_l in H; inversion H; destruct p; inversion H2. rewrite <- app_comm_cons in H.
      pose proof (pfoot_head_irrel p g v (src g e) e). unfold pfoot at 1 in H0. rewrite H0. apply IHp with l.
      inversion H. simpl. auto.
Qed.

Lemma epath_to_vpath_phead: forall g p l a, valid_path g p -> epath_to_vpath g p = a :: l -> phead p = a.
Proof.
  intros. destruct p. simpl. destruct l0; simpl in *. inversion H0; auto.
  destruct H. subst v. destruct l0; inversion H0; auto.
Qed.

Lemma pfoot_app_cons: forall g v1 v2 e l1 l2, pfoot g (v1, l1 ++ e :: l2) = pfoot g (v2, e :: l2).
Proof.
  intros. induction l1.
  + rewrite app_nil_l. apply pfoot_head_irrel.
  + rewrite <- app_comm_cons. rewrite <- IHl1. simpl. destruct (l1 ++ e :: l2) eqn:? ; auto.
    destruct l1; inversion Heql.
Qed.

Lemma pfoot_cons: forall g v e p, pfoot g (v, e :: p) = pfoot g (dst g e, p).
Proof.
  intros. destruct p; simpl; auto.
  destruct p; auto. apply (pfoot_head_irrel p g v (dst g e) e1).
Qed.

Lemma Subpath_refl: forall g p, Subpath g p p.
Proof.
  intros. destruct p as [v p]. split.
  + apply incl_refl.
  + left; auto.
Qed.

Lemma Subpath_trans: forall g p1 p2 p3, Subpath g p1 p2 -> Subpath g p2 p3 -> Subpath g p1 p3.
Proof.
  intros. destruct p1 as [v1 p1]. destruct p2 as [v2 p2]. destruct p3 as [v3 p3].
  destruct H, H0. split; unfold fst, snd in *. 1: apply incl_tran with p2; auto. destruct H1, H2.
  + subst v1 v2. left; auto.
  + subst. right; auto.
  + subst. destruct H1 as [e [? ?]]. right. exists e. split; auto.
  + destruct H1 as [e [? ?]]. right. exists e. split; auto.
Qed.

Lemma path_acyclic:
  forall (g: Gph) (p: path) n1 n2,
    path_endpoints g p n1 n2 -> valid_path g p -> Dup (epath_to_vpath g p) ->
    exists p', length (snd p') < length (snd p) /\ Subpath g p' p /\ path_endpoints g p' n1 n2 /\ valid_path g p'.
Proof.
  intros. apply Dup_cyclic in H1. destruct H1 as [a [L1 [L2 [L3 ?]]]]. rewrite <- app_comm_cons in H1.
  destruct (epath_to_vpath_split _ _ _ _ _ H0 H1) as [p1 [p2 [? [? [? [? ?]]]]]]. rewrite app_comm_cons in H6.
  destruct (epath_to_vpath_split _ _ _ _ _ H4 H6) as [p3 [p4 [? [? [? [? ?]]]]]]. exists (p1 +++ p4).
  split; [|split; [|split]];
  [destruct p as [v p]; destruct p1 as [v1 p1]; destruct p2 as [v2 p2]; destruct p3 as [v3 p3]; destruct p4 as [v4 p4]; unfold path_glue, fst, snd in * ..|].
  + clear - H2 H7 H10. inversion H2. subst p. rewrite !app_length. apply Plus.plus_lt_compat_l. inversion H7. rewrite app_length.
    destruct p3. 1: simpl in H10 |-* ; inversion H10; destruct L2; inversion H5. simpl; intuition.
  + clear - H2 H7. inversion H2. subst p. inversion H7. split. 2: left; simpl; auto. simpl. apply incl_app.
    * apply incl_appl, incl_refl. 
    * apply incl_appr, incl_appr, incl_refl.
  + inversion H2; subst. clear H2. inversion H7. subst. clear H7. destruct H. split; simpl in H; auto. destruct p4.
    - rewrite app_nil_r in *. apply epath_to_vpath_pfoot in H5. rewrite H5. simpl in H11. inversion H11. subst L3.
      replace (L1 ++ a :: L2 +:: a) with ((L1 ++ a :: L2) +:: a) in H1.
      * apply epath_to_vpath_pfoot in H1. rewrite H2 in H1. auto.
      * rewrite <- app_assoc. rewrite app_comm_cons. auto.
    - rewrite pfoot_app_cons with (v2 := v1). rewrite app_assoc in H2. rewrite pfoot_app_cons with (v2 := v1) in H2. auto.
  + apply valid_path_merge; auto. exists a. split. apply epath_to_vpath_pfoot in H5. auto.
    apply epath_to_vpath_phead in H11; auto.
Qed.

Lemma valid_path_acyclic:
  forall (g : Gph) (p : path) n1 n2,
    path_endpoints g p n1 n2 -> valid_path g p ->
    exists p', Subpath g p' p /\ path_endpoints g p' n1 n2 /\ NoDup (epath_to_vpath g p') /\ valid_path g p'.
Proof.
  intros until p. destruct p as [v p]. revert v. remember (length p). assert (length p <= n) by omega. clear Heqn. revert p H. induction n; intros.
  + assert (p = nil) by (destruct p; auto; simpl in H; exfalso; intuition). subst. exists (v, nil). simpl. simpl in H1.
    split. 1: apply Subpath_refl. do 2 (split; auto). constructor. intro; inversion H2. apply NoDup_nil.
  + destruct (NoDup_dec EV (epath_to_vpath g (v, p))).
    - exists (v, p); split; [apply Subpath_refl | split; auto].
    - destruct (path_acyclic _ _ _ _ H0 H1 n0) as [[v2 p2] [? [? [? ?]]]]. simpl in H2. assert (length p2 <= n) by intuition.
      specialize (IHn p2 H6 _ _ _ H4 H5). simpl in IHn, H3. destruct IHn as [p' [? ?]]. exists p'. split; auto.
      apply Subpath_trans with (v2, p2); auto.
Qed.

Lemma valid_path_edge: forall (g: Gph) v e p, valid_path g (v, e :: p) -> g |= v ~> (dst g e).
Proof.
  intros. destruct H. assert (strong_evalid g e) by (simpl in H0; destruct p; intuition).
  destruct H1 as [? [? ?]]. hnf. subst v. do 2 (split; auto).
  rewrite step_spec. exists e. auto.
Qed.

Lemma valid_path_cons_iff: forall g v e p, valid_path g (v, e :: p) <-> v = src g e /\ strong_evalid g e /\ valid_path g (dst g e, p).
Proof.
  intros. split; intros.
  + pose proof (valid_path_cons _ _ _ _ H). destruct H. subst v.
    do 2 (split; auto). simpl in H1. destruct p; intuition.
  + destruct H as [? [? ?]]. simpl in *. split; auto. destruct p; auto.
Qed.

Lemma path_prop_weaken: forall g (P1 P2 : Ensemble V) p,
  (forall d, P1 d -> P2 d) -> path_prop g P1 p -> path_prop g P2 p.
Proof.
  intros; hnf in *; intros; hnf in *; destruct p; destruct l.
  + apply H; auto.
  + unfold path_prop' in *. eapply Forall_impl; eauto.
    simpl. intuition.
Qed.

Lemma path_prop_subpath: forall g P p1 p2, Subpath g p1 p2 -> valid_path g p2 -> path_prop g P p2 -> path_prop g P p1.
Proof.
  intros. destruct p1 as [v1 p1]. destruct p2 as [v2 p2]. destruct H. unfold fst, snd in *. destruct H2.
  + subst. simpl in *. destruct p1, p2; auto.
    - destruct H0. subst. red in H1. rewrite Forall_forall in H1. assert (In e (e :: p2)) by apply in_eq. specialize (H1 _ H0). intuition.
    - hnf in H. assert (In e (e :: p1)) by apply in_eq. specialize (H _ H2). inversion H.
    - unfold path_prop' in *. eapply Forall_incl; eauto.
  + destruct H2 as [e [? ?]]. simpl in *. destruct p2. inversion H2. destruct p1.
    - red in H1. rewrite Forall_forall in H1. specialize (H1 _ H2). destruct H1. destruct H3; subst; auto.
    - unfold path_prop' in *. eapply Forall_incl; eauto.
Qed.

Lemma path_prop_tail: forall g P p, path_prop g P p -> path_prop g P (ptail g p).
Proof.
  intros. destruct p as [v p]. destruct p.
  + simpl in *. auto.
  + simpl in *. hnf in H. rewrite Forall_forall in H. destruct p.
    - assert (In e (e :: nil)) by apply in_eq. specialize (H _ H0). destruct H; auto.
    - hnf. rewrite Forall_forall. intros. apply H. simpl in *. right; auto.
Qed.

Lemma path_prop_equiv: forall g P p, valid_path g p -> (path_prop g P p <-> forall n, In_path g n p -> P n).
Proof.
  intros. destruct p as [v p]. split; intros.
  + destruct p; simpl in *.
    - unfold In_path in H1. simpl in H1. destruct H1. 1: subst; auto. destruct H1 as [e [? ?]]; exfalso; auto.
    - destruct H as [? _]. subst v. hnf in H0. rewrite Forall_forall in H0. unfold In_path in H1. unfold fst, snd in H1.
      destruct H1. 1: subst; assert (In e (e :: p)) by apply in_eq; destruct (H0 _ H); auto. destruct H as [e' [? ?]].
      destruct (H0 _ H). destruct H1; subst; auto.
  + destruct p; simpl in *.
    - apply H0. left; auto.
    - destruct H as [? _]. hnf. rewrite Forall_forall. subst. intros. split; apply H0; right; unfold fst, snd; exists x; split; auto.
Qed.

Lemma pfoot_in_cons: forall g e p v x, pfoot g (v, e :: p) = x -> exists e', In e' (e :: p) /\ dst g e' = x.
Proof.
  intros. revert v e H. induction p; intros. simpl in H.
  + exists e. split; auto. apply in_eq.
  + specialize (IHp (dst g e) a).
    assert (pfoot g (dst g e, a :: p) = x). {
      clear IHp. simpl in *. destruct p; auto.
      pose proof (pfoot_head_irrel p g v (dst g e) e0). unfold pfoot in H0.
      rewrite H in H0. auto.
    } specialize (IHp H0).
    destruct IHp as [e' [? ?]]. exists e'. split; auto.
    apply in_cons. auto.
Qed.

Lemma path_prop_split: forall (g: Gph) p1 p2 P, paths_meet g p1 p2 -> valid_path g (p1 +++ p2) -> path_prop g P (p1 +++ p2) -> (path_prop g P p1) /\ (path_prop g P p2).
Proof.
  intros. destruct p1 as [v1 p1]. destruct p2 as [v2 p2]. unfold path_glue, fst, snd in H0, H1. simpl. destruct p1, p2.
  + simpl in *. split; auto. destruct H as [? [? ?]]. simpl in *. subst v1. subst v2. auto.
  + destruct H as [? [? ?]]. simpl in H, H2. subst v1 v2. rewrite app_nil_l in * |-. simpl in H1. split; auto.
    destruct H0. subst. red in H1. rewrite Forall_forall in H1. assert (In e (e :: p2)) by apply in_eq. specialize (H1 _ H). intuition.
  + rewrite app_nil_r in H1. simpl in H1. split; auto. destruct H as [? [? ?]]. simpl in H2. subst v2.
    apply pfoot_in_cons in H. destruct H as [e' [? ?]]. subst x. red in H1. rewrite Forall_forall in H1.
    specialize (H1 _  H). destruct H1. apply H2.
  + simpl in H1. rewrite app_comm_cons in H1. red in H1. rewrite Forall_forall in H1. unfold path_prop'. rewrite !Forall_forall.
    split; intros; apply H1; apply in_or_app; [left | right]; auto.
Qed.

Lemma path_prop_app: forall g v p1 p2 P, valid_path g (v, p1 ++ p2) -> path_prop g P (v, p1 ++ p2) -> path_prop g P (v, p1) /\ path_prop g P (pfoot g (v, p1), p2).
Proof. intros. assert (paths_meet g (v, p1) (pfoot g (v, p1), p2)) by (exists (pfoot g (v, p1)); split; auto). apply path_prop_split; auto. Qed.

Lemma good_path_split: forall (g: Gph) p1 p2 P, paths_meet g p1 p2 -> good_path g P (p1 +++ p2) -> (good_path g P p1) /\ (good_path g P p2).
Proof.
  intros. destruct H0. apply path_prop_split in H1; auto. destruct H1.
  apply valid_path_split in H0; auto. destruct H0.
  unfold good_path. split; split; auto.
Qed.

Lemma good_path_app: forall g v p1 p2 P, good_path g P (v, p1 ++ p2) -> good_path g P (v, p1) /\ good_path g P (pfoot g (v, p1), p2).
Proof. intros. assert (paths_meet g (v, p1) (pfoot g (v, p1), p2)) by (exists (pfoot g (v, p1)); split; auto). apply good_path_split; auto. Qed.

Lemma path_prop_merge: forall (g: Gph) p1 p2 P, paths_meet g p1 p2 -> path_prop g P p1 -> path_prop g P p2 -> path_prop g P (p1 +++ p2).
Proof.
  intros. destruct p1 as [v1 p1]. destruct p2 as [v2 p2]. unfold path_glue, fst, snd. simpl in *. destruct p1, p2.
  + rewrite app_nil_r. auto.
  + rewrite app_nil_l. auto.
  + rewrite app_nil_r. auto.
  + rewrite <- app_comm_cons. rewrite app_comm_cons. unfold path_prop' in *. rewrite Forall_forall in *. intros.
    apply in_app_or in H2. destruct H2; [apply H0 | apply H1]; auto.
Qed.

Lemma good_path_merge: forall (g: Gph) p1 p2 P,
                         paths_meet g p1 p2 -> good_path g P p1 -> good_path g P p2 -> good_path g P (p1 +++ p2).
Proof.
  intros. destruct H0, H1. split.
  + apply valid_path_merge; auto.
  + apply path_prop_merge; auto.
Qed.

Lemma good_path_weaken: forall (g: Gph) p (P1 P2 : Ensemble V),
                          (forall d, P1 d -> P2 d) -> good_path g P1 p -> good_path g P2 p.
Proof.
  intros. split; destruct H0; auto.
  apply path_prop_weaken with P1; auto.
Qed.

Lemma good_path_acyclic:
  forall (g: Gph) P p n1 n2,
    path_endpoints g p n1 n2 -> good_path g P p -> exists p', path_endpoints g p' n1 n2 /\ NoDup (epath_to_vpath g p') /\ good_path g P p'.
Proof.
  intros. destruct H0. pose proof H0. apply valid_path_acyclic with (n1 := n1) (n2 := n2) in H0; trivial.
  destruct H0 as [p' [? [? [? ?]]]]. exists p'. do 3 (split; trivial).
  apply path_prop_subpath with p; trivial.
Qed.

Lemma good_path_tail: forall (g: Gph) P p, good_path g P p -> good_path g P (ptail g p).
Proof. intros. destruct H. split; [apply valid_path_tail | apply path_prop_tail]; auto. Qed.

Lemma reachable_by_is_reachable (g: Gph): forall n1 n2 P, g |= n1 ~o~> n2 satisfying P -> reachable g n1 n2.
Proof.
  intros. unfold reachable. destruct H as [l [? [? ?]]]. exists l.
  do 2 (split; auto). destruct l. hnf. destruct l; auto. hnf. rewrite Forall_forall; intros; auto.
Qed.

Lemma reachable_by_through_set_is_reachable_through_set (g: Gph):
  forall l n P, reachable_by_through_set g l P n -> reachable_through_set g l n.
Proof.
  intros.
  destruct H as [s [? ?]]; exists s; split; auto.
  apply reachable_by_is_reachable in H0; auto.
Qed.

Lemma reachable_by_path_is_reachable_by (g: Gph):
  forall p n1 n2 P, g |= p is n1 ~o~> n2 satisfying P -> g |= n1 ~o~> n2 satisfying P.
Proof. intros. exists p; auto. Qed.

Lemma reachable_by_path_weaken (g: Gph):
  forall p n1 n2 P1 P2, Included P1 P2 -> g |= p is n1 ~o~> n2 satisfying P1 -> g |= p is n1 ~o~> n2 satisfying P2.
Proof. intros. destruct H0 as [? ?]. split; auto. apply good_path_weaken with P1; auto. Qed.

Lemma reachable_by_path_is_reachable (g: Gph):
  forall p n1 n2 P, g |= p is n1 ~o~> n2 satisfying P -> reachable g n1 n2.
Proof. intros. apply reachable_by_path_is_reachable_by in H. apply reachable_by_is_reachable with P. auto. Qed.

Lemma reachable_Same_set (g: Gph) (S1 S2 : list V):
  S1 ~= S2 -> Same_set (reachable_through_set g S1) (reachable_through_set g S2).
Proof. intros; destruct H; split; repeat intro; destruct H1 as [y [HIn Hrch]]; exists y; split; auto. Qed.

(* Lemma reachable_by_path_nil: forall (g : Gph) n1 n2 P, ~ g |= nil is n1 ~o~> n2 satisfying P. *)
(* Proof. repeat intro. destruct H as [[? _] _]. disc. Qed. *)

Lemma reachable_by_path_head: forall (g: Gph) p n1 n2 P, g |= p is n1 ~o~> n2 satisfying P -> phead p = n1.
Proof. intros. destruct H as [[? _] _]. trivial. Qed.

Lemma reachable_by_path_foot: forall (g: Gph) p n1 n2 P, g |= p is n1 ~o~> n2 satisfying P -> pfoot g p = n2.
Proof. intros. destruct H as [[_ ?] _]. trivial. Qed.

Lemma reachable_by_path_merge: forall (g: Gph) p1 n1 n2 p2 n3 P,
                                 g |= p1 is n1 ~o~> n2 satisfying P ->
                                 g |= p2 is n2 ~o~> n3 satisfying P ->
                                 g |= (p1 +++ p2) is n1 ~o~> n3 satisfying P.
Proof.
  intros. destruct H. destruct H0.
  split. apply path_endpoints_glue with n2; auto.
  apply good_path_merge; auto.
  eapply path_endpoints_meet; eauto.
Qed.

Lemma reachable_by_path_split_glue:
  forall (g: Gph) P p1 p2 n1 n2 n, paths_meet_at g p1 p2 n ->
                                   g |= (p1 +++ p2) is n1 ~o~> n2 satisfying P ->
                                   g |= p1 is n1 ~o~> n satisfying P /\
                                   g |= p2 is n ~o~> n2 satisfying P.
Proof.
  intros. destruct H0 as [[? ?] ?]. apply good_path_split in H2.
  + destruct H2. destruct H. split; split; auto; split; auto.
    clear H2 H3. destruct p1 as [v1 p1]. destruct p2 as [v2 p2].
    unfold path_glue, fst, snd in * |-. destruct p2.
    - rewrite app_nil_r in * |-. simpl in *. rewrite H in H1. subst v2. auto.
    - rewrite pfoot_app_cons with (v2 := v1) in H1. rewrite pfoot_head_irrel with (v2 := v2) in H1. auto.
  + exists n; auto.
Qed.

Lemma pfoot_split: forall g v p1 e p2, valid_path g (v, p1 ++ e :: p2) -> pfoot g (v, p1) = src g e.
Proof.
  intros g v p1. revert v. induction p1; intros.
  + simpl. rewrite app_nil_l in H. destruct H. auto.
  + rewrite <- app_comm_cons in H. specialize (IHp1 (dst g a) e p2).
    apply valid_path_cons in H. specialize (IHp1 H). simpl. destruct p1.
    - simpl in IHp1. auto.
    - rewrite pfoot_head_irrel with (v2 := v) in IHp1. apply IHp1.
Qed.

Lemma reachable_by_path_split: forall (g: Gph) v p1 p2 n1 n2 P,
    g |= (v, p1 ++ p2) is n1 ~o~> n2 satisfying P -> g |= (v, p1) is n1 ~o~> pfoot g (v, p1) satisfying P /\ g |= (pfoot g (v, p1), p2) is pfoot g (v, p1) ~o~> n2 satisfying P.
Proof. intros. apply reachable_by_path_split_glue; [unfold paths_meet_at; simpl | unfold path_glue; unfold fst, snd]; auto. Qed.

Lemma reachable_by_path_app_cons: forall (g: Gph) v p1 e p2 n1 n2 P,
    g |= (v, p1 ++ e :: p2) is n1 ~o~> n2 satisfying P -> g |= (v, p1) is n1 ~o~> (src g e) satisfying P /\ g |= (dst g e, p2) is (dst g e) ~o~> n2 satisfying P.
Proof.
  intros. pose proof (reachable_by_path_split_glue g P (v, p1) (src g e, e :: p2) n1 n2 (src g e)).
  assert (paths_meet_at g (v, p1) (src g e, e :: p2) (src g e)) by (hnf; split; [apply (pfoot_split g v p1 e p2); destruct H as [_ [? _]] | simpl]; auto).
  specialize (H0 H1 H). destruct H0. split; auto.  pose proof (reachable_by_path_split_glue g P (src g e, e :: nil) (dst g e, p2) (src g e) n2 (dst g e)).
  assert (paths_meet_at g (src g e, e :: nil) (dst g e, p2) (dst g e)) by (hnf; simpl; auto). specialize (H3 H4 H2). destruct H3. auto.
Qed.

Lemma in_path_split: forall g p n, In_path g n p -> valid_path g p -> exists p1 p2, p = p1 +++ p2 /\ paths_meet_at g p1 p2 n.
Proof.
  intros. destruct p as [v p]. hnf in H. simpl in H. destruct H.
  + subst. exists (v, nil), (v, p). unfold path_glue. simpl. split; split; auto.
  + destruct H as [e [? ?]]. destruct (in_split _ _ H) as [p1 [p2 ?]]. destruct H1.
    - exists (v, p1), (src g e, e :: p2). unfold path_glue. simpl. subst p. split; auto.
      subst n. split; auto. apply pfoot_split in H0. auto.
    - exists (v, p1 +:: e), (dst g e, p2). unfold path_glue. simpl. subst p. rewrite <- app_assoc.
      rewrite <- app_comm_cons. rewrite app_nil_l. split; auto. split.
      * rewrite pfoot_last. auto.
      * simpl. auto.
Qed.

Lemma reachable_by_path_split_in: forall (g : Gph) P p n n1 n2,
  g |= p is n1 ~o~> n2 satisfying P ->
  In_path g n p -> exists p1 p2, p = p1 +++ p2 /\
                                 g |= p1 is n1 ~o~> n satisfying P /\
                                 g |= p2 is n ~o~> n2 satisfying P.
Proof.
  intros. apply in_path_split in H0.
  + destruct H0 as [p1 [p2 [? ?]]]. subst p. exists p1, p2. split; auto.
    apply reachable_by_path_split_glue; auto.
  + destruct H as [? [? ?]]; auto.
Qed.

(* Lemma reachable_by_path_Forall: forall (g: Gph) p n1 n2 P, *)
(*   g |= p is n1 ~o~> n2 satisfying P -> Forall P p. *)
(* Proof. intros. destruct H as [_ [_ ?]]. apply H. Qed. *)

Lemma reachable_by_path_In: forall (g: Gph) p n1 n2 P n,
  g |= p is n1 ~o~> n2 satisfying P -> In_path g n p -> P n.
Proof.
  intros. destruct H as [_ [? ?]]. destruct p as [v p]. hnf in H0. simpl in *. destruct p, H0.
  + subst; auto.
  + destruct H0 as [e [? _]]. inversion H0.
  + subst. destruct H. hnf in H1. rewrite Forall_forall in H1. assert (In e (e :: p)) by apply in_eq.
    specialize (H1 _ H2). subst v. intuition.
  + destruct H0 as [e' [? ?]]. hnf in H1. rewrite Forall_forall in H1. specialize (H1 _ H0).
    destruct H1. destruct H2; subst n; auto.
Qed.

Lemma pfoot_si: forall (g1 g2: Gph) p, g1 ~=~ g2 -> valid_path g1 p -> pfoot g1 p = pfoot g2 p.
Proof.
  intros. destruct p as [v p]. revert v H0. induction p; intros.
  + simpl. auto.
  + simpl. destruct p.
    - simpl in H0. destruct H0 as [? [? [? ?]]]. destruct H as [? [? [? ?]]]. specialize (H4 a). apply H6; intuition.
    - specialize (IHp (dst g1 a)). apply valid_path_cons in H0. specialize (IHp H0). 
      pose proof (pfoot_head_irrel p g1 v (dst g1 a) e). pose proof (pfoot_head_irrel p g2 v (dst g1 a) e). unfold pfoot in *.
      rewrite H1, H2. apply IHp.
Qed.

Lemma valid_path_strong_evalid: forall g v p e, valid_path g (v, p) -> In e p -> strong_evalid g e.
Proof.
  intros g v p. revert v. induction p; intros. 1: inversion H0. simpl in H0. destruct H0.
  + subst. destruct H. simpl in H0. destruct p; intuition.
  + apply valid_path_cons in H. specialize (IHp _ _ H H0). auto.  
Qed.

Lemma In_path_si: forall (g1 g2: Gph) p x, g1 ~=~ g2 -> valid_path g1 p -> (In_path g1 x p <-> In_path g2 x p).
Proof.
  cut (forall g1 g2 p x, g1 ~=~ g2 -> valid_path g1 p -> In_path g1 x p -> In_path g2 x p); intros.
  + split; intros; [apply H with g1 | apply H with g2]; auto. 1: symmetry; auto. apply valid_path_si with g1; auto. symmetry; auto.
  + destruct p as [v p]. unfold In_path in *. simpl in H1 |-* . destruct H1; [left | right]; auto.
    destruct H1 as [e [? ?]]. exists e. split; auto. destruct (valid_path_strong_evalid _ _ _ _ H0 H1) as [? [? ?]]. destruct H as [? [? [? ?]]]. specialize (H6 e).
    assert (src g1 e = src g2 e) by (apply H7; intuition). assert (dst g1 e = dst g2 e) by (apply H8; intuition). rewrite <- H9, <- H10. auto.
Qed.

Lemma path_prop_si: forall (g1 g2: Gph) P p, g1 ~=~ g2 -> valid_path g1 p -> path_prop g1 P p -> path_prop g2 P p.
Proof.
  intros. destruct p as [v p]. destruct p; simpl in H1 |-* ; auto. unfold path_prop' in *. rewrite Forall_forall in *.
  intros. specialize (H1 _ H2). destruct H as [_ [? [? ?]]]. specialize (H x). specialize (H3 x). specialize (H4 x).
  destruct (valid_path_strong_evalid _ _ _ _ H0 H2) as [? _].
  rewrite <- H3; [|intuition..]. rewrite <- H4; intuition.
Qed.

Lemma reachable_by_path_si: forall (g1 g2: Gph) p n1 n2 P,
    g1 ~=~ g2 -> (g1 |= p is n1 ~o~> n2 satisfying P <-> g2 |= p is n1 ~o~> n2 satisfying P).
Proof.
  cut (forall g1 g2 p n1 n2 P, g1 ~=~ g2 -> g1 |= p is n1 ~o~> n2 satisfying P -> g2 |= p is n1 ~o~> n2 satisfying P); intros.
  + split; intros; [apply (H g1 g2) | apply (H g2 g1)]; auto. symmetry; auto.
  + destruct H0 as [[? ?] [? ?]]. split; split; auto.
    - rewrite <- (pfoot_si g1 g2 p); auto.
    - rewrite <- (valid_path_si g1 g2 H); auto.
    - apply (path_prop_si g1); auto.
Qed.

Lemma in_path_or_cons: forall g v e p n, v = src g e -> (In_path g n (v, e :: p) <-> n = v \/ In_path g n (dst g e, p)).
Proof.
  intros. subst. unfold In_path. simpl. intuition.
  + destruct H0 as [e0 [? ?]]. destruct H. 1: subst; intuition. right; right; exists e0. split; auto.
  + right. exists e. intuition.
  + right. destruct H as [? [? ?]]. exists x. intuition.
Qed.

Lemma valid_path_valid: forall (g : Gph) p n, valid_path g p -> In_path g n p -> vvalid g n.
Proof.
  intros g p. destruct p as [v p]. revert v. induction p; intros.
  + simpl in *. hnf in H0. simpl in H0. destruct H0. 1: subst; auto. destruct H0 as [e [? _]]. inversion H0.
  + rewrite in_path_or_cons in H0. 2: destruct H; auto. destruct H0.
    - subst. destruct H. subst. simpl in H0. destruct p; [|destruct H0 as [H0 _]]; destruct H0 as [_ [? _]]; auto.
    - apply valid_path_cons in H. apply (IHp (dst g a)); auto.
Qed.

Lemma valid_path_evalid: forall (g : Gph) v p e, valid_path g (v, p) -> In e p -> evalid g e.
Proof. intros. apply (valid_path_strong_evalid g v) in H0; auto. destruct H0; auto. Qed.

Lemma pfoot_in: forall g p n, pfoot g p = n -> In_path g n p.
Proof.
  intros. destruct p as [v p]. destruct p.
  + simpl in H. subst. left. simpl; auto.
  + apply pfoot_in_cons in H. right. unfold snd. destruct H as [e' [? ?]].
    exists e'. split; auto.
Qed.

Lemma pfoot_spec: forall g p n, pfoot g p = n <-> p = (n, nil) \/ exists v l e, p = (v, l +:: e) /\ dst g e = n.
Proof.
  intros. destruct p as [h p]. revert h. induction p; intros; split; intros.
  + simpl in H. subst; left; auto.
  + simpl in *. destruct H. 1: inversion H; auto. destruct H as [? [? [? [? ?]]]]. inversion H. destruct x0; inversion H3.
  + right. rewrite pfoot_cons in H. rewrite IHp in H. destruct H.
    - inversion H. subst p. exists h, nil, a. simpl. auto.
    - destruct H as [v [l [e [? ?]]]]. inversion H. exists h, (a :: l), e. simpl. auto.
  + destruct H. inversion H. destruct H as [v [l [e [? ?]]]]. rewrite pfoot_cons. rewrite IHp. destruct l.
    - simpl in H. inversion H. subst. left; auto.
    - simpl in H. right. exists (dst g a), l, e. inversion H. auto.
Qed.

(******************************************

Reachable Lemmas
 
******************************************)

Lemma reachable_by_refl: forall (g : Gph) n (P: V -> Prop), vvalid g n -> P n -> g |= n ~o~> n satisfying P.
Proof.
  intros.
  exists (n, nil). split. compute. auto.
  split. simpl. trivial. auto. 
Qed.

Lemma reachable_by_trans: forall (g: Gph) n1 n2 n3 P,
  g |= n1 ~o~> n2 satisfying P ->
  g |= n2 ~o~> n3 satisfying P ->
  g |= n1 ~o~> n3 satisfying P.
Proof. do 2 destruct 1. exists (x +++ x0). apply reachable_by_path_merge with n2; auto. Qed.

Lemma reachable_by_through_set_reachable_by: forall (g: Gph) l x y P,
  reachable_by_through_set g l P x -> reachable_by g x P y -> reachable_by_through_set g l P y.
Proof.
  intros.
  destruct H as [s [? ?]]; exists s; split; auto.
  apply reachable_by_trans with x; auto.
Qed.

Lemma reachable_by_head_valid: forall (g : Gph) n1 n2 P, g |= n1 ~o~> n2 satisfying P -> vvalid g n1.
Proof.
  repeat intro. destruct H as [p [[? _] [? _]]]. destruct p as [v p]. simpl in *. subst.
  destruct p; auto. destruct H0. simpl in H0. subst. destruct p; [|destruct H0 as [H0 _]]; destruct H0 as [? [? ?]]; auto.
Qed.

Lemma reachable_by_foot_valid: forall (g : Gph) n1 n2 P, g |= n1 ~o~> n2 satisfying P -> vvalid g n2.
Proof.
  repeat intro. destruct H as [p [[? ?] [? ?]]]. apply pfoot_in in H0.
  apply (valid_path_valid _ _ n2) in H1; auto.
Qed.

Lemma reachable_by_head_prop: forall (g: Gph) n1 n2 P, g |= n1 ~o~> n2 satisfying P -> P n1.
Proof.
  intros. destruct H as [p ?]. eapply reachable_by_path_In; eauto.
  apply reachable_by_path_head in H. destruct p as [v p]. simpl in H. subst. left; auto.
Qed.

Lemma reachable_by_foot_prop: forall (g: Gph) n1 n2 P, g |= n1 ~o~> n2 satisfying P -> P n2.
Proof.
  intros. destruct H as [p ?]. eapply reachable_by_path_In; eauto.
  apply reachable_by_path_foot in H. apply pfoot_in. trivial.
Qed.

Lemma reachable_by_through_set_foot_valid: forall (g : Gph) S n P, reachable_by_through_set g S P n -> vvalid g n.
Proof.
  intros.
  destruct H as [s [? ?]].
  eapply reachable_by_foot_valid with (n1 := s); eauto.
Qed.

Lemma reachable_by_through_set_foot_prop: forall (g : Gph) S n P, reachable_by_through_set g S P n -> P n.
Proof.
  intros.
  destruct H as [s [? ?]].
  eapply reachable_by_foot_prop with (n1 := s); eauto.
Qed.

Lemma edge_P_reachable_by: forall (g: Gph) n1 n2 (P: Ensemble V), P n1 -> P n2 -> g |= n1 ~> n2 -> g |= n1 ~o~> n2 satisfying P.
Proof.
  intros. destruct H1 as [? [? ?]]. rewrite step_spec in H3. destruct H3 as [e [? [? ?]]].
  exists (n1, e :: nil). split; split; auto.
  + simpl. split; auto. split; intuition. rewrite H4. auto. rewrite H5; auto.
  + simpl. hnf. rewrite Forall_forall. intros. simpl in H6. destruct H6; [|inversion H6].
    subst. intuition.
Qed.

Lemma edge_reachable_by:
  forall (g: Gph) n1 n2 n3 (P: Ensemble V),
     P n1 ->
     g |= n1 ~> n2 ->
     g |= n2 ~o~> n3 satisfying P ->
     g |= n1 ~o~> n3 satisfying P.
Proof.
  intros. apply reachable_by_trans with n2; auto.
  apply reachable_by_head_prop in H1.
  apply edge_P_reachable_by; auto.
Qed.

Lemma step_reachable_by:
  forall (g: Gph) n1 n2 n3 (P: Ensemble V),
     vvalid g n1 ->
     P n1 ->
     step g n1 n2 ->
     g |= n2 ~o~> n3 satisfying P ->
     g |= n1 ~o~> n3 satisfying P.
Proof.
  intros.
  eapply edge_reachable_by; eauto.
  split; [| split]; auto.
  apply reachable_by_head_valid in H2; auto.
Qed.

Lemma reachable_by_edge:
  forall (g: Gph) n1 n2 n3 (P: Ensemble V),
     P n3 ->
     g |= n1 ~o~> n2 satisfying P ->
     g |= n2 ~> n3 ->
     g |= n1 ~o~> n3 satisfying P.
Proof.
  intros. apply reachable_by_trans with n2; auto.
  apply reachable_by_foot_prop in H0.
  apply edge_P_reachable_by; auto.
Qed.

Lemma reachable_by_step:
  forall (g: Gph) n1 n2 n3 (P: Ensemble V),
     vvalid g n3 ->
     P n3 ->
     g |= n1 ~o~> n2 satisfying P ->
     step g n2 n3 ->
     g |= n1 ~o~> n3 satisfying P.
Proof.
  intros.
  eapply reachable_by_edge; eauto.
  split; [| split]; auto.
  apply reachable_by_foot_valid in H1; auto.
Qed.

Lemma reachable_by_through_set_edge:
  forall (g: Gph) l n2 n3 (P: Ensemble V),
     P n3 ->
     reachable_by_through_set g l P n2 ->
     edge g n2 n3 ->
     reachable_by_through_set g l P n3.
Proof.
  intros.
  destruct H0 as [s [? ?]].
  exists s; split; auto.
  apply reachable_by_edge with n2; auto.
Qed.

Lemma reachable_by_through_set_step:
  forall (g: Gph) l n2 n3 (P: Ensemble V),
     vvalid g n3 ->
     P n3 ->
     reachable_by_through_set g l P n2 ->
     step g n2 n3 ->
     reachable_by_through_set g l P n3.
Proof.
  intros.
  eapply reachable_by_through_set_edge; eauto.
  split; [| split]; auto.
  apply reachable_by_through_set_foot_valid in H1; auto.
Qed.

Lemma reachable_refl: forall (g: Gph) x, vvalid g x -> reachable g x x.
Proof. intros; apply reachable_by_refl; auto. Qed.

Lemma reachable_trans: forall (g: Gph) x y z,
  reachable g x y -> reachable g y z -> reachable g x z.
Proof. intros. eapply reachable_by_trans; eauto. Qed.

Lemma reachable_through_set_reachable: forall (g: Gph) l x y,
  reachable_through_set g l x -> reachable g x y -> reachable_through_set g l y.
Proof.
  intros.
  destruct H as [s [? ?]]; exists s; split; auto.
  apply reachable_trans with x; auto.
Qed.

Lemma reachable_head_valid: forall (g : Gph) n1 n2, reachable g n1 n2 -> vvalid g n1.
Proof. intros; eapply reachable_by_head_valid; eauto. Qed.

Lemma reachable_foot_valid: forall (g : Gph) n1 n2, reachable g n1 n2 -> vvalid g n2.
Proof. intros; eapply reachable_by_foot_valid; eauto. Qed.

Lemma reachable_through_set_foot_valid: forall (g : Gph) S n, reachable_through_set g S n -> vvalid g n.
Proof.
  intros.
  destruct H as [s ?].
  apply reachable_foot_valid with s; tauto.
Qed.

Lemma edge_reachable:
  forall (g : Gph) x y z, reachable g y z -> edge g x y -> reachable g x z.
Proof. intros. eapply edge_reachable_by; eauto. Qed.

Lemma step_reachable:
  forall (g : Gph) x y z, step g x y -> reachable g y z -> vvalid g x -> reachable g x z.
Proof. intros. eapply step_reachable_by; eauto. Qed.

Lemma reachable_edge:
  forall (g : Gph) x y z, reachable g x y -> edge g y z -> reachable g x z.
Proof. intros. eapply reachable_by_edge; eauto. Qed.

Lemma reachable_step:
  forall (g : Gph) x y z, reachable g x y -> step g y z -> vvalid g z -> reachable g x z.
Proof. intros. eapply reachable_by_step; eauto. Qed.

Lemma reachable_through_set_edge:
  forall (g: Gph) l n2 n3,
     reachable_through_set g l n2 ->
     edge g n2 n3 ->
     reachable_through_set g l n3.
Proof.
  intros.
  destruct H as [s [? ?]].
  exists s; split; auto.
  apply reachable_edge with n2; auto.
Qed.

Lemma reachable_through_set_step:
  forall (g: Gph) l n2 n3,
     vvalid g n3 ->
     reachable_through_set g l n2 ->
     step g n2 n3 ->
     reachable_through_set g l n3.
Proof.
  intros.
  eapply reachable_through_set_edge; eauto.
  split; [| split]; auto.
  apply reachable_through_set_foot_valid in H0; auto.
Qed.

(******************************************

Other Reachable Lemmas
 
******************************************)

Lemma reachable_acyclic: forall (g: Gph) n1 P n2,
  g |= n1 ~o~> n2 satisfying P <->
  g |= n1 ~~> n2 satisfying P.
Proof.
  split; intros.
  destruct H as [p [? ?]].
  apply (good_path_acyclic g P p n1 n2 H) in H0.
  destruct H0 as [p' [? ?]].
  exists p'. destruct H1. split; auto. split; auto.
  destruct H as [p [? ?]].
  exists p. trivial.
Qed.

Lemma reachable_by_subset_reachable: forall (g: Gph) n P,
  Included (reachable_by g n P) (reachable g n).
Proof.
  repeat intro. unfold reachable.
  destruct H as [p [? [? ?]]]. exists p.
  split; trivial.
  split; trivial. apply path_prop_weaken with P; auto.
Qed.

Lemma reachable_through_empty (g: Gph):
  Same_set (reachable_through_set g nil) (Empty_set V).
Proof.
  split; repeat intro.
  destruct H; destruct H; apply in_nil in H; tauto.
  hnf in H; tauto.
Qed.

Lemma reachable_through_empty_eq (g: Gph):
  forall S, Same_set (reachable_through_set g S) (Empty_set V) <-> forall y, In y S -> ~ vvalid g y.
Proof.
  intros; split.
  + induction S; intros; [unfold In; intros; tauto |].
    intros.
    destruct (in_inv H0).
    - subst a; intro.
      destruct H. specialize (H y).
      spec H; [| inversion H].
      unfold Ensembles.In. exists y.
      split; [apply in_eq | apply reachable_by_refl; [|hnf]; trivial].
    - assert (Same_set (reachable_through_set g (a :: S)) (reachable_through_set g S)).
      Focus 1. {
        split.
        + apply Extensionality_Ensembles in H; rewrite H.
          intro x; intro. inversion H2.
        + intro; intros. destruct H2 as [s [? ?]]. 
          exists s; split; trivial; apply in_cons; trivial.
      } Unfocus.
      rewrite <- H2 in IHS. pose proof (IHS H y).
      apply H3; trivial.
  + intros. split; repeat intro.
    destruct H0 as [y [? ?]]. apply H in H0. apply reachable_head_valid in H1; tauto. hnf in H0; tauto.
Qed.

Lemma reachable_through_set_eq (g: Gph):
  forall a S x, reachable_through_set g (a :: S) x <-> reachable g a x \/ reachable_through_set g S x.
Proof.
  intros; split; intros. destruct H as [s [? ?]]. apply in_inv in H. destruct H. subst. left; auto. right. exists s.
  split; auto. destruct H. exists a. split. apply in_eq. auto. destruct H as [s [? ?]]. exists s. split. apply in_cons. auto.
  auto.
Qed.

Lemma reachable_path_in:
  forall (g: Gph) (p: path) (l y : V), g |= p is l ~o~> y satisfying (fun _ : V => True) ->
                                                   forall z, In_path g z p -> reachable g l z.
Proof.
  intros. apply reachable_by_path_split_in with (n := z) in H; auto.
  destruct H as [p1 [p2 [? [? ?]]]]. exists p1. apply H1.
Qed.

Lemma reachable_by_path_in: forall (g: Gph) (p: path) (l y : V) (P: V -> Prop),
    g |= p is l ~o~> y satisfying P -> forall z, In_path g z p -> g |= l ~o~> z satisfying P.
Proof.
  intros. apply reachable_by_path_split_in with (n := z) in H; auto.
  destruct H as [p1 [p2 [? [? ?]]]]. exists p1. apply H1.
Qed.

Lemma reachable_path_in':
  forall (g: Gph) (p: path) (l y : V), g |= p is l ~o~> y satisfying (fun _ : V => True) ->
                                         forall z, In_path g z p -> reachable g z y.
Proof.
  intros. apply reachable_by_path_split_in with (n := z) in H; auto.
  destruct H as [p1 [p2 [? [? ?]]]]. exists p2. apply H2.
Qed.

Lemma reachable_by_path_in': forall (g: Gph) (p: path) (l y : V) (P: V -> Prop),
    g |= p is l ~o~> y satisfying P -> forall z, In_path g z p -> g |= z ~o~> y satisfying P.
Proof.
  intros. apply reachable_by_path_split_in with (n := z) in H; auto.
  destruct H as [p1 [p2 [? [? ?]]]]. exists p2. apply H2.
Qed.

Lemma reachable_list_permutation:
  forall (g: Gph) x l1 l2,
    reachable_list g x l1 -> reachable_list g x l2 -> NoDup l1 -> NoDup l2 -> Permutation l1 l2.
Proof. intros. apply NoDup_Permutation; auto. intro y. rewrite (H y), (H0 y). tauto. Qed.

Lemma reachable_through_set_single:
  forall (g: Gph) x y, reachable_through_set g (x :: nil) y <-> reachable g x y.
Proof.
  intros.
  unfold reachable_through_set; split; intros.
  + destruct H as [? [[? | ?] ?]]; [subst; auto |].
    inversion H.
  + exists x; split; auto.
    left; auto.
Qed.

Lemma reachable_through_set_single':
  forall (g: Gph) x, Same_set (reachable_through_set g (x :: nil)) (reachable g x).
Proof.
  intros.
  rewrite Same_set_spec; intros y.
  apply reachable_through_set_single.
Qed.

Lemma reachable_valid_and_through_single:
  forall (g: Gph) {x y}, reachable g x y -> (vvalid g y /\ reachable_through_set g (x :: nil) y).
Proof.
  intros. split.
  + apply reachable_foot_valid in H; auto.
  + exists x. split.
    - apply in_eq.
    - auto.         
Qed.

Lemma reachable_list_EnumCovered: forall (g: Gph) x l, reachable_list g x l -> EnumCovered V (reachable g x).
Proof.
  unfold reachable_list, EnumCovered, Ensembles.In.
  intros.
  exists (nodup equiv_dec l).
  split.
  + apply NoDup_nodup.
  + intros y ?.
    specialize (H y).
    rewrite nodup_In.
    tauto.
Qed.

Lemma reachable_set_list_EnumCovered: forall (g: Gph) S l, reachable_set_list g S l -> EnumCovered V (reachable_through_set g S).
Proof.
  unfold reachable_set_list, EnumCovered, Ensembles.In.
  intros.
  exists (nodup equiv_dec l).
  split.
  + apply NoDup_nodup.
  + intros y ?.
    specialize (H y).
    rewrite nodup_In.
    tauto.
Qed.

Lemma epath_to_vpath_cons_eq: forall g v e p, v = src g e -> epath_to_vpath g (v, e :: p) = v :: epath_to_vpath g (dst g e, p).
Proof.
  intros. remember (epath_to_vpath g (v, e :: p)) as l. destruct l. 1: simpl in Heql; destruct p; inversion Heql.
  symmetry in Heql. rewrite (epath_to_vpath_cons _ _ _ _ _ _ Heql). f_equal. subst.
  simpl in Heql. destruct p; inversion Heql; auto.
Qed.

Lemma in_path_eq_epath_to_vpath: forall g p x, valid_path g p -> (In x (epath_to_vpath g p) <-> In_path g x p).
Proof.
  intros. destruct p as [v p]. revert v H. induction p; intros.
  + simpl. unfold In_path. simpl. intuition. destruct H1 as [e [? _]]; exfalso; auto.
  + pose proof (valid_path_cons _ _ _ _ H). destruct H as [? _]. specialize (IHp _ H0).
    rewrite epath_to_vpath_cons_eq; auto. rewrite in_path_or_cons; auto. rewrite <- IHp.
    simpl. intuition.
Qed.

Lemma NoDup_epath_to_vpath_edge: forall g p, valid_path g p -> NoDup (epath_to_vpath g p) -> forall e, In e (snd p) -> src g e <> dst g e.
Proof.
  intros g p. destruct p as [v p]. revert v; induction p; intros. 1: simpl in H1; inversion H1. simpl in H1. destruct H1.
  + subst. simpl in H. destruct H. simpl in H0. destruct p.
    - apply NoDup_cons_2 in H0. intro. apply H0. rewrite H2. apply in_eq.
    - destruct H1 as [? [? ?]]. apply NoDup_cons_2 in H0. intro. apply H0. clear H0. rewrite H4. rewrite H2. destruct p; apply in_eq.
  + rewrite valid_path_cons_iff in H. destruct H as [? [? ?]]. rewrite epath_to_vpath_cons_eq in H0; auto. unfold snd in IHp.
    apply IHp with (dst g a); auto. apply NoDup_cons_1 in H0. auto.
Qed.

Lemma reachable_by_ind: forall (g: Gph) x y P,
                           g |= x ~o~> y satisfying P -> x = y \/
                                                         exists z, g |= x ~> z /\
                                                                   g |= z ~o~> y satisfying (fun n => P n /\ n <> x).
Proof.
  intros. rewrite reachable_acyclic in H. destruct (equiv_dec x y). 1: left; auto. right.
  destruct H as [path [? [[? ?] [? ?]]]]. destruct path as [v p]. simpl in H0. subst v.
  destruct p. 1: simpl in H1; exfalso; auto. exists (dst g e). destruct H2. split.
  + subst x. assert (strong_evalid g e) by (simpl in H2; destruct p; intuition).
    destruct H0 as [? [? ?]]. do 2 (split; auto). rewrite step_spec. exists e. intuition.
  + exists (dst g e, p). split; split.
    - simpl; auto.
    - rewrite pfoot_cons in H1; auto.
    - apply valid_path_cons with x. split; auto.
    - clear H1. simpl in H3. simpl. destruct p.
      * subst x. clear H2. simpl in *. hnf in H3. rewrite Forall_forall in H3. assert (In e (e :: nil)) by apply in_eq. specialize (H3 _ H0). destruct H3.
        apply NoDup_cons_2 in H. simpl in H. split; auto.
      * unfold path_prop' in *. rewrite Forall_forall in *. intros. assert (In x0 (e :: e0 :: p)) by (apply in_cons; auto). specialize (H3 _ H4).
        destruct H3. rewrite epath_to_vpath_cons_eq in H; auto. clear H4. apply NoDup_cons_2 in H.
        rewrite in_path_eq_epath_to_vpath in H. 2: apply valid_path_cons with x; simpl; auto.
        split; split; auto; intro; apply H; unfold In_path; unfold fst, snd; right; exists x0; split; intuition.
Qed.

Lemma reachable_by_weaken: forall (g: Gph) x y P Q,
                                  Included P Q ->
                                  g |= x ~o~> y satisfying P ->
                                  g |= x ~o~> y satisfying Q.
Proof.
  intros. destruct H0 as [p [? [? ?]]].
  exists p. do 2 (split; auto). apply path_prop_weaken with P; auto.
Qed.

Lemma reachable_by_ind_equiv:
  forall (g: PreGraph V E) n1 l n2 (P: Ensemble V),
     let P' := Intersection _ P (Complement _ (eq n1)) in
     vvalid g n1 ->
     step_list g n1 l ->
     P n1 ->
     (g |= n1 ~o~> n2 satisfying P <->
     n1 = n2 \/ reachable_by_through_set g l P' n2).
Proof.
  intros.
  split; intros.
  + apply reachable_by_ind in H2.
    destruct H2; [auto | right].
    destruct H2 as [n [[? [? ?]] ?]].
    exists n.
    split; [rewrite (H0 n); auto |].
    eapply reachable_by_weaken; [| eauto].
    clear.
    intro n; unfold P', Ensembles.In.
    rewrite Intersection_spec.
    unfold Complement, Ensembles.In.
    assert (n <> n1 <-> n1 <> n) by (split; intros; congruence).
    tauto.
  + destruct H2.
    - subst; eapply reachable_by_refl; auto.
    - destruct H2 as [n [? ?]].
      rewrite (H0 n) in H2.
      apply edge_reachable_by with n.
      * auto.
      * split; [| split]; auto.
        apply reachable_by_head_valid in H3; auto.
      * eapply reachable_by_weaken; [| eauto].
        apply Intersection1_Included, Included_refl.
Qed.

Lemma reachable_by_through_set_weaken:
  forall (g: Gph) l x P Q,
    Included P Q ->
    reachable_by_through_set g l P x ->
    reachable_by_through_set g l Q x.
Proof.
  intros.
  destruct H0 as [s [? ?]].
  exists s; split; auto.
  eapply reachable_by_weaken; eauto.
Qed.

Lemma reachable_by_eq: forall (g: Gph) x y P Q,
                                  (forall z, P z <-> Q z) ->
                                  (g |= x ~o~> y satisfying P <-> g |= x ~o~> y satisfying Q).
Proof.
  intros until y.
  intros; split; apply reachable_by_weaken; firstorder.
Qed.

Lemma reachable_through_set_app: forall g S1 S2 x,
  reachable_through_set g S1 x \/ reachable_through_set g S2 x <-> reachable_through_set g (S1 ++ S2) x.
Proof.
  intros; split; intros; [destruct H as [[s ?] | [s ?]] | destruct H as [s ?]].
  + exists s; split; [| tauto].
    rewrite in_app_iff; tauto.
  + exists s; split; [| tauto].
    rewrite in_app_iff; tauto.
  + rewrite in_app_iff in H; destruct H as [[? | ?] ?]; [left | right];
    exists s; tauto.
Qed.

Lemma reachable_through_set_app_left: forall g S1 S2 x,
  reachable_through_set g S1 x -> reachable_through_set g (S1 ++ S2) x.
Proof.
  intros.
  rewrite <- reachable_through_set_app; tauto.
Qed.

Lemma reachable_through_set_app_right: forall g S1 S2 x,
  reachable_through_set g S2 x -> reachable_through_set g (S1 ++ S2) x.
Proof.
  intros.
  rewrite <- reachable_through_set_app; tauto.
Qed.

Lemma reachable_by_through_nil: forall g P n, reachable_by_through_set g nil P n <-> False.
Proof.
  intros; split; intro.
  + destruct H as [s [? ?]]. inversion H.
  + exfalso; auto.
Qed.

Lemma reachable_by_through_nil': forall g P, Same_set (reachable_by_through_set g nil P) (Empty_set _).
Proof.
  intros.
  rewrite Same_set_spec; intro n'.
  pose proof Empty_set_iff V n'.
  unfold Ensembles.In in H.
  rewrite H.
  apply reachable_by_through_nil.
Qed.

Lemma reachable_by_through_singleton:
  forall g P n1 n2, reachable_by_through_set g (n1 :: nil) P n2 <-> g |= n1 ~o~> n2 satisfying P.
Proof.
  intros. unfold reachable_by_through_set; split; intro.
  + destruct H as [s [? ?]]. simpl in H. destruct H; [subst | exfalso]; auto.
  + exists n1. split; [apply in_eq | auto].
Qed.

Lemma reachable_by_through_singleton':
  forall g P n, Same_set (reachable_by_through_set g (n :: nil) P) (reachable_by g n P).
Proof.
  intros.
  rewrite Same_set_spec; intro n'.
  apply reachable_by_through_singleton.
Qed.

Lemma reachable_by_through_app: forall g P n l1 l2, reachable_by_through_set g (l1 ++ l2) P n <-> reachable_by_through_set g l1 P n \/ reachable_by_through_set g l2 P n.
Proof.
  intros.
  unfold reachable_by_through_set.
  split; [intros [s [? ?]] | intros [[s [? ?]] | [s [? ?]]]].
  + rewrite in_app_iff in H.
    destruct H; [left | right]; exists s; auto.
  + exists s.
    rewrite in_app_iff; auto.
  + exists s.
    rewrite in_app_iff; auto.
Qed.

Lemma reachable_by_through_app': forall g P l1 l2,
  Same_set
   (reachable_by_through_set g (l1 ++ l2) P)
   (Union _ (reachable_by_through_set g l1 P) (reachable_by_through_set g l2 P)).
Proof.
  intros.
  rewrite Same_set_spec; intro n; rewrite Union_spec.
  apply reachable_by_through_app.
Qed.

Lemma reachable_by_through_non_foot: forall g P n l l0, reachable_by_through_set g l P n -> reachable_by_through_set g (l ++ l0 :: nil) P n.
Proof.
  intros.
  rewrite reachable_by_through_app; tauto.
Qed.

Lemma reachable_by_through_foot: forall g P n l l0, reachable_by g l0 P n -> reachable_by_through_set g (l ++ l0 :: nil) P n.
Proof.
  intros.
  rewrite reachable_by_through_app, reachable_by_through_singleton; tauto.
Qed.

Definition ReachDecidable (g: Gph) (x : V) (P : V -> Prop) :=
  forall y, Decidable (g |= x ~o~> y satisfying P).

Lemma is_tree_sub_is_tree: forall (g: Gph) root, vvalid g root -> is_tree g root -> forall v, step g root v -> is_tree g v.
Proof.
  repeat intro. assert (reachable g root y) by (apply step_reachable with v; auto). specialize (H0 _ H3).
  destruct H0 as [proot [? ?]]. destruct H2 as [p ?]. exists p. split; auto. intro p'. intros.
  rewrite  step_spec in H1. destruct H1 as [e [? [? ?]]].
  assert (forall path, g |= path is v ~o~> y satisfying (fun _ : V => True) -> g |= (root, e :: nil) +++ path is root ~o~> y satisfying (fun _ : V => True)). {
    intro ppp; intros. clear -H H1 H6 H7 H8. apply reachable_by_path_merge with v; auto.
    split; split; simpl; auto.
    + split; auto. hnf. apply reachable_by_path_is_reachable in H8. apply reachable_by_head_valid in H8. subst. auto.
    + hnf. rewrite Forall_forall; intros; auto.
  } pose proof (H8 _ H2). pose proof (H8 _ H5). pose proof (H4 _ H9). pose proof (H4 _ H10). rewrite H11 in H12. inversion H12.
  destruct p as [v1 p1]. destruct p' as [v2 p2]. simpl in H14. f_equal; auto.
  clear -H2 H5. apply reachable_by_path_head in H2. simpl in H2. apply reachable_by_path_head in H5. simpl in H5. subst. auto.
Qed.

Lemma root_reachable_by_derive: forall (P: V -> Prop) g root,
    forall n, g |= root ~o~> n satisfying P ->
              n = root \/
              exists e, out_edges g root e /\ g |= dst g e ~o~> n
                                                satisfying (fun x : V => P x /\ x <> root).
Proof.
  intros. apply reachable_by_ind in H. destruct H; [left | right]; auto.
  destruct H as [z [[? [? ?]] ?]]. rewrite step_spec in H1. destruct H1 as [e [? [? ?]]]. subst z.
  exists e; split; auto. hnf. auto.
Qed.

Lemma In_path_glue: forall g p1 p2 v, In_path g v (p1 +++ p2) -> In_path g v p1 \/ In_path g v p2.
Proof.
  intros. destruct p1 as [v1 p1]. destruct p2 as [v2 p2]. unfold path_glue in H. simpl in H. unfold In_path in *. simpl in *. destruct H. 1: left; left; auto.
  destruct H as [e [? ?]]. rewrite in_app_iff in H. destruct H; [left | right]; right; exists e; split; auto.
Qed.

Lemma valid_path_reachable: forall g p v1 v2, valid_path g p -> In_path g v1 p -> In_path g v2 p -> reachable g v1 v2 \/ reachable g v2 v1.
Proof.
  intros. assert (g |= p is (phead p) ~o~> (pfoot g p) satisfying (fun _ => True)) by (split; split; simpl; auto; rewrite path_prop_equiv; intros; auto).
  destruct (reachable_by_path_split_in _ _ _ _ _ _ H2 H0) as [p1 [p2 [? [? ?]]]]. rewrite H3 in H1. apply In_path_glue in H1. destruct H1.
  + right. apply (reachable_path_in' _ _ _ _ H4); auto.
  + left. apply (reachable_path_in _ _ _ _ H5); auto.
Qed.

Lemma In_path_Subpath: forall g p1 p2 v, In_path g v p1 -> Subpath g p1 p2 -> In_path g v p2.
Proof.
  intros. destruct p1 as [v1 p1]. destruct p2 as [v2 p2]. unfold In_path in H. destruct H0. simpl in *. destruct H.
  + subst. auto.
  + right. destruct H as [e [? ?]]. exists e. split; auto. 
Qed.
  
End PATH_LEM.

Arguments path_glue {_ _} _ _.

Module PathNotation.
Notation "p1 '+++' p2" := (path_glue p1 p2) (at level 20, left associativity).
End PathNotation.

Notation " g '|=' p 'is' n1 '~o~>' n2 'satisfying' P" := (reachable_by_path g p n1 P n2) (at level 1).
Notation " g '|=' n1 '~o~>' n2 'satisfying' P " := (reachable_by g n1 P n2) (at level 1).
Notation " g '|=' n1 '~~>' n2 'satisfying' P " := (reachable_by_acyclic g n1 P n2) (at level 1).
