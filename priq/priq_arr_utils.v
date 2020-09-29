Require Import VST.floyd.proofauto.
Require Import CertiGraph.lib.List_ext.

Definition SIZE := 8.
Definition inf := Int.max_signed - 1.

Lemma inf_eq: inf = 2147483646.
Proof. compute; trivial. Qed.

Lemma inf_eq2: Int.sub (Int.repr 2147483647)
                       (Int.repr 1) = Int.repr inf.
Proof. compute. trivial. Qed.

Lemma SIZE_rep: 0 <= priq_arr_utils.SIZE <= Int.max_signed.
Proof. unfold priq_arr_utils.SIZE. set (i:=Int.max_signed); compute in i; subst i. lia. Qed.

Lemma SIZE_rep': 0 < priq_arr_utils.SIZE <= Int.max_signed.
Proof. unfold priq_arr_utils.SIZE. set (i:=Int.max_signed); compute in i; subst i. lia. Qed.

Lemma inf_rep: 0 <= priq_arr_utils.inf <= Int.max_signed.
Proof. set (i:=Int.max_signed); compute in i; subst i. rewrite inf_eq.
lia. Qed.

Lemma inf_repable:
repable_signed inf.
Proof.
unfold repable_signed, SIZE. rewrite inf_eq.
set (j:=Int.min_signed); compute in j; subst j.
set (j:=Int.max_signed); compute in j; subst j.
lia.
Qed.

Global Opaque inf.

(** UTILITIES TO HELP WITH VERIF OF ARRAY-BASED PQ **)

(* a weight to be added cannot be inf + 1 *)
Definition weight_inrange_priq item :=
  Int.min_signed <= item <= inf.

(* over time, the overall PQ can range from MIN to inf + 1 *)
Definition inrange_priq (priq : list Z) :=
  Forall (fun x => Int.min_signed <= x <= inf + 1) priq.

Definition isEmpty (priq : list Z) : val :=
  fold_right (fun h acc => if (Z_lt_dec h (inf + 1)) then Vzero else acc) Vone priq.

Fixpoint find {A: Type} {EA: EquivDec.EqDec A eq} (l : list A) (n : A) (ans : Z) :=
  match l with
  | [] => ans
  | h :: t => if EA h n
              then ans
              else (find t n (1 + ans))
  end.

(** LEMMAS ABOUT THESE UTILITIES **)

Lemma isEmpty_in: forall l target,
    In target l -> target < inf + 1 -> isEmpty l = Vzero.
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

Lemma isEmpty_in': forall l,
    (exists i, In i l /\ i < (inf + 1)) <-> isEmpty l = Vzero.
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

Lemma isEmptyTwoCases: forall l,
    isEmpty l = Vone \/ isEmpty l = Vzero.
Proof.
  intros. induction l. 1: simpl; left; trivial.
  destruct IHl; simpl; destruct (Z_lt_dec a (inf+1));
    (try now left); now right.
Qed.

Lemma isEmptyMeansInf: forall l,
    isEmpty l = Vone -> Forall (fun x => x > inf) l.
Proof.
  intros. induction l; trivial. simpl in H.
  destruct (Z_lt_dec a (inf+1)); [inversion H|].
  specialize (IHl H). apply Forall_cons; trivial. lia.
Qed.

Lemma find_index_gen: forall {A:Type} {EA: EquivDec.EqDec A eq} {d: Inhabitant A} (l: list A) i ans,
    0 <= i < Zlength l ->
    ~ In (Znth i l) (sublist 0 i l) ->
    find l (Znth i l) ans = i + ans.
Proof.
  intros. generalize dependent i.
  generalize dependent ans. induction l.
  1: intros; rewrite Zlength_nil in H; exfalso; lia.
  unfold find.
  intros.
  destruct (EA a (Znth i (a :: l))).
  - rewrite <- e in H0. clear - H H0.
    destruct (Z.eq_dec 0 i). 1: lia.
    destruct H. assert (0 < i) by lia.
    exfalso. apply H0.
    unfold sublist. replace (i-0) with i by lia. simpl.
    replace (Z.to_nat i) with (Z.to_nat (Z.succ (i-1))) by rep_lia.
    rewrite Z2Nat.inj_succ by lia.
    rewrite firstn_cons. apply in_eq.
  - unfold RelationClasses.complement, Equivalence.equiv in c.
    destruct (Z.eq_dec 0 i).
    rewrite <- e in c; rewrite Znth_0_cons in c. contradiction.
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

Lemma find_index: forall {A:Type} {EA: EquivDec.EqDec A eq} {d: Inhabitant A} (l: list A) i,
    0 <= i < Zlength l ->
    ~ In (Znth i l) (sublist 0 i l) ->
    find l (Znth i l) 0 = i.
Proof.
  intros. replace i with (i + 0) at 2 by lia.
  apply find_index_gen; trivial.
Qed.

Lemma find_range_gen: forall {A:Type} {EA: EquivDec.EqDec A eq} {d: Inhabitant A} (l: list A) target ans,
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
    destruct (EA target target).
    rewrite Zlength_cons. split; rep_lia.
    unfold RelationClasses.complement, Equivalence.equiv in c; contradiction.
  - unfold find. destruct (EA a target).
    1: rewrite Zlength_cons; split; rep_lia.
    assert (0 <= 1 + ans) by lia.
    pose proof (IHl (1+ans) H1 target H).
    clear -H2. unfold find in H2.
    rewrite Zlength_cons. rep_lia.
Qed.

Lemma find_range: forall {A:Type} {EA: EquivDec.EqDec A eq} {d: Inhabitant A} (l: list A) target,
    In target l ->
    0 <= find l target 0 < Zlength l.
Proof.
  intros. replace (Zlength l) with (Zlength l + 0) by lia.
  apply find_range_gen; trivial; lia.
Qed.

Lemma Znth_find_gen:
  forall {A:Type} {EA: EquivDec.EqDec A eq} {d: Inhabitant A} (l: list A) target ans,
    0 <= ans ->
    In target l ->
    Znth ((find l target ans)-ans) l = target.
Proof.
  intros. generalize dependent ans.
  induction l. 1: inversion H0.
  intros.
  destruct H0.
  - subst target. simpl.
    destruct (EA a a).
    + replace (ans-ans) with 0 by lia.
      rewrite Znth_0_cons; auto.
    + unfold RelationClasses.complement, Equivalence.equiv in c; contradiction.
  - specialize (IHl H0).
    simpl.
    destruct (EA a target).
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
  forall {A:Type} {EA: EquivDec.EqDec A eq} {d: Inhabitant A} (l: list A) target,
    In target l ->
    Znth (find l target 0) l = target.
Proof.
  intros.
  replace (find l target 0) with (find l target 0 - 0) by lia.
  apply Znth_find_gen; [lia | assumption].
Qed.

Lemma find_app_In1:
forall {A:Type} {EA: EquivDec.EqDec A eq} (l1 l2: list A) v ans, In v l1 -> find (l1++l2) v ans = find l1 v ans.
Proof.
induction l1; intros. contradiction.
destruct (EA v a). hnf in e. subst a.
simpl.
destruct (EA v v). auto. unfold RelationClasses.complement, Equivalence.equiv in c; contradiction.
destruct H. symmetry in H; contradiction.
simpl. destruct (EA a v). symmetry in e; contradiction.
rewrite IHl1; auto.
Qed.

Lemma find_accum_add1:
forall {A:Type} {EA: EquivDec.EqDec A eq} (l: list A) v ans1 ans2, find l v (ans1+ans2) = ans1 + find l v ans2.
Proof.
induction l; intros.
simpl. auto.
simpl. destruct (EA a v). auto.
replace (1+(ans1+ans2)) with (ans1 + (1+ans2)) by lia. apply IHl.
Qed.

Lemma find_app_notIn1:
forall {A:Type} {EA: EquivDec.EqDec A eq} (l1: list A) l2 v ans, ~ In v l1 -> find (l1++l2) v ans = Zlength l1 + find l2 v ans.
Proof.
induction l1; intros. rewrite app_nil_l, Zlength_nil. lia.
assert (~ In v l1). unfold not; intros; apply H. right; auto.
simpl. destruct (EA a v). hnf in e; subst a. exfalso. apply H. left; auto.
rewrite Zlength_cons. rewrite IHl1; auto.
rewrite <- Z.add_1_r, <- Z.add_assoc. rewrite find_accum_add1. auto.
Qed.

Corollary find_notIn:
forall {A:Type} {EA: EquivDec.EqDec A eq} (l: list A) v ans, ~ In v l -> find l v ans = Zlength l + ans.
Proof.
intros. replace l with (l++nil). rewrite find_app_notIn1. simpl.
rewrite app_nil_r; auto.
auto. apply app_nil_r.
Qed.

Corollary find_notIn_0:
forall {A:Type} {EA: EquivDec.EqDec A eq} (l: list A) v, ~ In v l -> find l v 0 = Zlength l.
Proof. intros. rewrite find_notIn by auto. rewrite Z.add_0_r; auto. Qed.

Lemma find_In_ubound:
forall {A:Type} {EA: EquivDec.EqDec A eq} (l: list A) v ans, In v l -> find l v ans < Zlength l + ans.
Proof.
induction l; intros. contradiction.
rewrite Zlength_cons.
simpl. destruct (EA a v).
pose proof (Zlength_nonneg l); lia.
rewrite Z.add_succ_l. rewrite find_accum_add1, Z.add_1_l.
assert (find l v ans < Zlength l + ans). apply IHl. destruct H. contradiction. auto.
lia.
Qed.

Lemma find_ubound:
forall {A:Type} {EA: EquivDec.EqDec A eq} (l: list A) v ans, find l v ans <= Zlength l + ans.
Proof.
induction l; intros. rewrite Zlength_nil; simpl; lia.
rewrite Zlength_cons.
simpl. destruct (EA a v).
pose proof (Zlength_nonneg l); lia.
rewrite Z.add_succ_l. rewrite find_accum_add1, Z.add_1_l.
specialize IHl with v ans.
lia.
Qed.

Lemma find_cons:
forall {A:Type} {EA: EquivDec.EqDec A eq} (l: list A) v ans, find (v::l) v ans = ans.
Proof.
intros. simpl. destruct (EA v v). auto. unfold RelationClasses.complement, Equivalence.equiv in c; contradiction.
Qed.

Lemma find_lbound:
forall {A:Type} {EA: EquivDec.EqDec A eq} (l: list A) v ans, ans <= find l v ans.
Proof.
induction l; intros. simpl. lia.
simpl. destruct (EA a v). lia.
rewrite find_accum_add1. specialize IHl with v ans; lia.
Qed.

Lemma find_app_le:
forall {A:Type} {EA: EquivDec.EqDec A eq} (l1: list A) l2 v ans, find l1 v ans <= find (l1++l2) v ans.
Proof.
induction l1; intros.
rewrite app_nil_l. simpl. apply find_lbound.
simpl. destruct (EA a v). lia.
do 2 rewrite find_accum_add1. specialize IHl1 with l2 v ans. lia.
Qed.

Lemma find_eq:
forall {A:Type} {EA: EquivDec.EqDec A eq} (l: list A) x y acc, NoDup l -> In x l -> In y l -> find l x acc = find l y acc -> x = y.
Proof.
induction l; intros. contradiction.
destruct H0; destruct H1.
++
subst x; subst y. auto.
++
subst x. rewrite find_cons in H2.
simpl in H2. destruct (EA a y). hnf in e; subst y. apply NoDup_cons_2 in H; contradiction.
rewrite find_accum_add1 in H2. pose proof (find_lbound l y acc). lia.
++
subst y. rewrite find_cons in H2.
simpl in H2. destruct (EA a x). hnf in e; subst x. apply NoDup_cons_2 in H; contradiction.
rewrite find_accum_add1 in H2. pose proof (find_lbound l x acc). lia.
++
simpl in H2. destruct (EA a x). hnf in e; subst x. apply NoDup_cons_2 in H; contradiction.
destruct (EA a y). hnf in e; subst y. apply NoDup_cons_2 in H; contradiction.
do 2 rewrite find_accum_add1 in H2. apply (IHl x y acc).
apply NoDup_cons_1 in H; auto. auto. auto. lia.
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

Instance Z_EqDec: EquivDec.EqDec Z eq.
Proof. hnf. apply Z.eq_dec. Qed.

Lemma find_src: forall src,
    0 <= src < SIZE ->
    find (upd_Znth src (list_repeat (Z.to_nat SIZE) inf) 0)
         (fold_right Z.min (hd 0 (upd_Znth src (list_repeat (Z.to_nat SIZE) inf) 0))
                     (upd_Znth src (list_repeat (Z.to_nat SIZE) inf) 0)) 0 = src.
Proof.
  intros.
  remember (upd_Znth src (list_repeat (Z.to_nat SIZE) inf) 0) as l.
  replace (fold_right Z.min (hd 0 l) l) with (Znth src l).
  - apply find_index.
    1: rewrite Heql, upd_Znth_Zlength; trivial.
    rewrite Heql.
    rewrite upd_Znth_same; trivial.
    rewrite sublist_upd_Znth_l.
    2: lia.
    2: rewrite Zlength_list_repeat; lia.
    rewrite sublist_list_repeat by lia.
    replace (src - 0) with (src) by lia.
    intro. apply in_list_repeat in H0.
    inversion H0.
  - subst l.
    rewrite upd_Znth_same; trivial.
    rewrite upd_Znth_unfold at 2; auto.
    repeat rewrite fold_right_app.
    repeat rewrite sublist_list_repeat; try lia.
    2: rewrite Zlength_list_repeat; [|unfold SIZE]; lia.
    repeat rewrite Zlength_list_repeat by lia.
    replace (src - 0) with (src) by lia.
    rewrite <- Znth_0_hd.
    2: { unfold SIZE in *; rewrite upd_Znth_Zlength by assumption.
         rewrite Zlength_list_repeat; lia. }
    destruct (Z.eq_dec src 0).
    + rewrite e. rewrite upd_Znth_same. simpl.
      compute; trivial. rewrite Zlength_list_repeat; lia.
    + rewrite upd_Znth_diff;
        try rewrite Zlength_list_repeat; try lia.
      rewrite Znth_list_repeat_inrange by (unfold SIZE in *; lia).
      simpl. rewrite Z.min_l.
      1,2: rewrite min_picks_first.
      all: try lia; compute; inversion 1.
Qed.

Lemma fold_min_in_list: forall l, Zlength l > 0 -> In (fold_right Z.min (hd 0 l) l) l.
Proof.
  intros. apply min_in_list.
  - apply incl_refl.
  - rewrite <- Znth_0_hd by (unfold SIZE in *; lia). apply Znth_In; lia.
Qed.

Lemma find_min_lt_inf: forall u l,
    u = find l (fold_right Z.min (hd 0 l) l) 0 -> isEmpty l = Vzero ->
    Zlength l > 0 -> Znth u l < inf + 1.
Proof.
  intros. rewrite <- isEmpty_in' in H0. destruct H0 as [? [? ?]].
  rewrite H. rewrite Znth_find.
  - pose proof (fold_min _ _ H0). lia.
  - now apply fold_min_in_list.
Qed.
