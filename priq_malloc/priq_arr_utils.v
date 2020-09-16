Require Import VST.floyd.proofauto.

(*
On their way out.

Definition SIZE := 8.
Definition inf := Int.max_signed - Int.max_signed / SIZE.

Lemma inf_eq: inf = 1879048192.
Proof. compute; trivial. Qed.

Lemma inf_eq2: Int.sub (Int.repr 2147483647)
                       (Int.divs (Int.repr 2147483647)
                                 (Int.repr 8)) = Int.repr inf.
Proof. compute. trivial. Qed.

Global Opaque inf.
 *)

(** UTILITIES TO HELP WITH VERIF OF ARRAY-BASED PQ **)

(* a weight to be added cannot be inf + 1 *)
Definition weight_inrange_priq item inf :=
  Int.min_signed <= item <= inf.

(* over time, the overall PQ can range from MIN to inf + 1 *)
Definition inrange_priq (priq : list Z) inf :=
  Forall (fun x => Int.min_signed <= x <= inf + 1) priq.

Definition isEmpty (priq : list Z) inf : val :=
  fold_right (fun h acc => if (Z_lt_dec h (inf + 1)) then Vzero else acc) Vone priq.

Fixpoint find (l : list Z) (n : Z) (ans : Z) :=
  match l with
  | [] => ans
  | h :: t => if eq_dec h n
              then ans
              else (find t n (1 + ans))
  end.


(** LEMMAS ABOUT THESE UTILITIES **)

Lemma isEmpty_in: forall l target inf,
    In target l -> target < inf + 1 -> isEmpty l inf = Vzero.
Proof.
  intros. induction l.
  1: exfalso; apply (in_nil H).
  unfold isEmpty. rewrite fold_right_cons.
  destruct (Z_lt_dec a (inf+1)); trivial.
  simpl in H; simpl; destruct H.
  1: rewrite H in n; exfalso; lia.
  clear n a. specialize (IHl H).
  unfold isEmpty in IHl. trivial.
Qed.

Lemma isEmpty_in': forall l inf,
    (exists i, In i l /\ i < (inf + 1)) <-> isEmpty l inf = Vzero.
Proof.
  split; intros.
  - destruct H as [? [? ?]]. induction l.
    1: exfalso; apply (in_nil H).
    unfold isEmpty. rewrite fold_right_cons.
    destruct (Z_lt_dec a (inf+1)); trivial.
    simpl in H; simpl; destruct H.
    1: rewrite H in n; exfalso; lia.
    clear n a. specialize (IHl H).
    unfold isEmpty in IHl. trivial.
  - induction l.
    1: inversion H.
    simpl in H. destruct (Z_lt_dec a (inf+1)).
    + exists a. split; simpl; [left|]; trivial.
    + destruct (IHl H) as [? [? ?]].
      exists x. split; [apply in_cons|]; assumption.
Qed.

Lemma isEmptyTwoCases: forall l inf,
    isEmpty l inf = Vone \/ isEmpty l inf = Vzero.
Proof.
  intros. induction l. 1: simpl; left; trivial.
  destruct IHl; simpl; destruct (Z_lt_dec a (inf+1));
    (try now left); now right.
Qed.

Lemma isEmptyMeansInf: forall l inf,
    isEmpty l inf = Vone <-> Forall (fun x => x > inf) l.
Proof.
  intros.
  split; intros.
  - induction l; trivial. simpl in H.
    destruct (Z_lt_dec a (inf+1)); [inversion H|].
    specialize (IHl H). apply Forall_cons; trivial. lia.
  - induction l; trivial. simpl.
    destruct (Z_lt_dec a (inf+1)).
    2: { apply IHl.
         rewrite Forall_forall; intros.
         rewrite Forall_forall in H. simpl in H.
         apply H. right; trivial.
    }
    exfalso.
    rewrite Forall_forall in H.
    assert (In a (a :: l)) by (apply in_eq).
    specialize (H _ H0). lia.
Qed.

Lemma isEmpty_Vone_app: forall l1 l2 inf,
    isEmpty (l1 ++ l2) inf = Vone <->
    isEmpty l1 inf = Vone /\ isEmpty l2 inf = Vone.
Proof.
  intros. split; intros.
  - repeat rewrite isEmptyMeansInf, Forall_forall in *;
      split; intros; apply H, in_or_app;
        [left | right]; trivial.
  - repeat rewrite isEmptyMeansInf, Forall_forall in *.
    destruct H. intros.
    apply in_app_or in H1; destruct H1;
      [apply H | apply H0]; trivial.
Qed.
    
Lemma find_index_gen: forall l i ans,
    0 <= i < Zlength l ->
    ~ In (Znth i l) (sublist 0 i l) ->
    find l (Znth i l) ans = i + ans.
Proof.
  intros. generalize dependent i.
  generalize dependent ans. induction l.
  1: intros; rewrite Zlength_nil in H; exfalso; lia.
  unfold find.
  intros.
  destruct (eq_dec a (Znth i (a :: l))).
  - rewrite <- e in H0. clear - H H0.
    destruct (Z.eq_dec 0 i). 1: lia.
    destruct H. assert (0 < i) by lia.
    exfalso. apply H0.
    unfold sublist. replace (i-0) with i by lia. simpl.
    replace (Z.to_nat i) with (Z.to_nat (Z.succ (i-1))) by rep_lia.
    rewrite Z2Nat.inj_succ by lia.
    rewrite firstn_cons. apply in_eq.
  - destruct (Z.eq_dec 0 i).
    1: rewrite <- e in n; rewrite Znth_0_cons in n;
      exfalso; lia.
    assert (0 <= i - 1 < Zlength l) by
        (rewrite Zlength_cons in H; rep_lia).
    assert (~ In (Znth (i - 1) l) (sublist 0 (i - 1) l)). {
      rewrite <- (Znth_pos_cons i l a) by lia.
      rewrite <- (sublist_1_cons l a i).
      intro. apply H0.
      apply (sublist_In 1 i).
      rewrite sublist_sublist0 by lia. assumption.
    }
    pose proof (IHl (1 + ans) (i - 1) H1 H2).
    replace (i - 1 + (1 + ans)) with (i + ans) in H3 by lia.
    replace (Znth i (a :: l)) with (Znth (i - 1) l).
    2: { symmetry. apply Znth_pos_cons; lia. }
    rewrite <- H3.
    unfold find. trivial.
Qed.

Lemma find_index: forall l i,
    0 <= i < Zlength l ->
    ~ In (Znth i l) (sublist 0 i l) ->
    find l (Znth i l) 0 = i.
Proof.
  intros. replace i with (i + 0) at 2 by lia.
  apply find_index_gen; trivial.
Qed.

Lemma find_range_gen: forall l target ans,
    In target l ->
    0 <= ans ->
    ans <= find l target ans < Zlength l + ans.
Proof.
  intros. generalize dependent target.
  generalize dependent ans.
  induction l.
  1: intros; simpl; now rewrite Zlength_nil.
  intros. apply in_inv in H. destruct H.
  - subst a. unfold find.
    destruct (eq_dec target target).
    rewrite Zlength_cons. split; rep_lia.
    exfalso; lia.
  - unfold find. destruct (eq_dec a target).
    1: rewrite Zlength_cons; split; rep_lia.
    assert (0 <= 1 + ans) by lia.
    pose proof (IHl (1+ans) H1 target H).
    clear -H2. unfold find in H2.
    rewrite Zlength_cons. rep_lia.
Qed.

Lemma find_range: forall l target,
    In target l ->
    0 <= find l target 0 < Zlength l.
Proof.
  intros. replace (Zlength l) with (Zlength l + 0) by lia.
  apply find_range_gen; trivial; lia.
Qed.

Lemma Znth_find_gen:
  forall l target ans,
    0 <= ans ->
    In target l ->
    Znth ((find l target ans)-ans) l = target.
Proof.
  intros. generalize dependent ans.
  induction l. 1: inversion H0.
  intros.
  destruct H0.
  - subst target. simpl.
    destruct (initial_world.EqDec_Z a a).
    + replace (ans-ans) with 0 by lia.
      rewrite Znth_0_cons; auto.
    + exfalso; lia.
  - specialize (IHl H0).
    simpl.
    destruct (initial_world.EqDec_Z a target).
    + replace (ans-ans) with 0 by lia.
      rewrite Znth_0_cons; auto.
    + assert (0 <= 1 + ans) by lia.
      specialize (IHl (1+ans) H1).
      rewrite Znth_pos_cons.
      replace (1+ans) with (ans+1) in IHl at 2 by lia.
      rewrite Z.sub_add_distr in IHl.
      assumption.
      destruct (find_range_gen l target (1+ans) H0 H1) as [? _].
      lia.
Qed.

Lemma Znth_find:
  forall l target,
    In target l ->
    Znth (find l target 0) l = target.
Proof.
  intros.
  replace (find l target 0) with (find l target 0 - 0) by lia.
  apply Znth_find_gen; [lia | assumption].
Qed.

Lemma Forall_fold_min:
  forall (f: Z -> Prop) (x: Z) (al: list Z),
    f x -> Forall f al -> f (fold_right Z.min x al).
Proof.
  intros. induction H0.
  simpl. auto. simpl. unfold Z.min at 1.
  destruct (Z.compare x0 (fold_right Z.min x l)) eqn:?; auto.
Qed.

Lemma fold_min_another:
  forall x al y,
    fold_right Z.min x (al ++ [y]) = Z.min (fold_right Z.min x al) y.
Proof.
  intros. revert x; induction al; simpl; intros.
  apply Z.min_comm. rewrite <- Z.min_assoc. f_equal. apply IHal.
Qed.

Theorem fold_min_general:
  forall (al: list Z)(i: Z),
    In i (al) ->
    forall x, List.fold_right Z.min x al <= i.
Proof.
  induction al; intros. 1: inversion H.
  destruct H.
  1: subst a; simpl; apply Z.le_min_l.
  simpl. rewrite Z.le_min_r. apply IHal, H.
  Qed.

Theorem fold_min:
  forall (al: list Z)(i: Z),
    In i (al) ->
    List.fold_right Z.min (hd 0 al) al <= i.
Proof. intros. apply fold_min_general, H. Qed.

Lemma min_not_in_prev i l :
  Znth i l < fold_right Z.min (Znth 0 l) (sublist 0 i l) ->
  ~ In (Znth i l) (sublist 0 i l).
Proof.
  intros. intro.
  pose proof (fold_min_general (sublist 0 i l) (Znth i l) H0(Znth 0 l)). lia.
Qed.

Lemma min_in_list : forall l1 l2 starter,
    incl l1 l2 ->
    In starter l2 ->
    In (fold_right Z.min starter l1) l2.
Proof.
  intros. induction l1; trivial. simpl.
  destruct (Z.min_dec a (fold_right Z.min starter l1));
    rewrite e; clear e.
  apply H, in_eq.
  apply IHl1, (incl_cons_inv H).
Qed.

Lemma Znth_0_hd:
  forall list, Zlength list > 0 -> Znth 0 list = hd 0 list.
Proof.
  intros. induction list; inversion H.
  rewrite Znth_0_cons. trivial.
Qed.

Lemma min_picks_first:
  forall num mono start,
    start <= mono ->
    fold_right Z.min start (list_repeat num mono) = start.
Proof.
  intros. induction num; trivial.
  simpl. rewrite IHnum. rewrite Z.min_r; lia.
Qed.

Lemma find_src: forall src size inf,
    0 < inf ->
    0 <= src < size ->
    find (upd_Znth src (list_repeat (Z.to_nat size) inf) 0)
         (fold_right Z.min (hd 0 (upd_Znth src (list_repeat (Z.to_nat size) inf) 0))
                     (upd_Znth src (list_repeat (Z.to_nat size) inf) 0)) 0 = src.
Proof.
  intros.
  assert (Ha: 0 <= src < Zlength (list_repeat (Z.to_nat size) inf)). {
    rewrite Zlength_list_repeat; lia.
  }

  remember (upd_Znth src (list_repeat (Z.to_nat size) inf) 0) as l.
  replace (fold_right Z.min (hd 0 l) l) with (Znth src l).
  - apply find_index.
    1: rewrite Heql, upd_Znth_Zlength;
      rewrite Zlength_list_repeat; lia.
    rewrite Heql.
    rewrite upd_Znth_same; trivial.
    rewrite sublist_upd_Znth_l.
    2: lia.
    2: rewrite Zlength_list_repeat; lia.
    rewrite sublist_list_repeat by lia.
    replace (src - 0) with (src) by lia.
    intro. apply in_list_repeat in H1. lia.
  - subst l.
    rewrite upd_Znth_same; trivial.
    rewrite upd_Znth_unfold at 2; auto.
    repeat rewrite fold_right_app.
    repeat rewrite sublist_list_repeat; try lia.
    2: rewrite Zlength_list_repeat; lia.
    repeat rewrite Zlength_list_repeat by lia.
    replace (src - 0) with (src) by lia.
    rewrite <- Znth_0_hd.
    2: { rewrite upd_Znth_Zlength by assumption.
         rewrite Zlength_list_repeat; lia. }
    destruct (Z.eq_dec src 0).
    + rewrite e. rewrite upd_Znth_same.
      2: rewrite Zlength_list_repeat; lia.
      simpl. rewrite Z.min_l; trivial.
      rewrite min_picks_first; lia.
    + rewrite upd_Znth_diff;
        try rewrite Zlength_list_repeat; try lia.
      rewrite Znth_list_repeat_inrange by lia.
      simpl. rewrite Z.min_l.
      1,2: rewrite min_picks_first.
      all: try lia; compute; inversion 1.
Qed.

Lemma fold_min_in_list: forall l, Zlength l > 0 -> In (fold_right Z.min (hd 0 l) l) l.
Proof.
  intros. apply min_in_list.
  - apply incl_refl.
  - rewrite <- Znth_0_hd by trivial. apply Znth_In; lia.
Qed.

Lemma find_min_lt_inf: forall u l inf,
    u = find l (fold_right Z.min (hd 0 l) l) 0 -> isEmpty l inf = Vzero ->
    Zlength l > 0 -> Znth u l < inf + 1.
Proof.
  intros. rewrite <- isEmpty_in' in H0. destruct H0 as [? [? ?]].
  rewrite H. rewrite Znth_find.
  - pose proof (fold_min _ _ H0). lia.
  - now apply fold_min_in_list.
Qed.
