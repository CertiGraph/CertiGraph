(* Require Import VST.floyd.proofauto.
   TEMPORARILY replace "floyd.proofauto"
   with all the imports in the list below.
   This reduces makefile-based recompilation
   when changing things in (e.g.) forward.v
*)
Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.closed_lemmas.
Require Import VST.floyd.nested_pred_lemmas.
Require Import VST.floyd.nested_field_lemmas.
Require Import VST.floyd.efield_lemmas.
Require Import VST.floyd.mapsto_memory_block.
Require Import VST.floyd.reptype_lemmas.
Require VST.floyd.aggregate_pred. Import VST.floyd.aggregate_pred.aggregate_pred.
Require Import VST.floyd.data_at_rec_lemmas.
Require Import VST.floyd.field_at.
Require Import VST.floyd.nested_loadstore.
(*Require Import VST.floyd.unfold_data_at.*)
Require Import VST.floyd.entailer.
(*  End TEMPORARILY *)

Lemma int64_eq_e: forall i j, Int64.eq i j = true -> i=j.
Proof. intros. pose proof (Int64.eq_spec i j); rewrite H in H0; auto. Qed.

Lemma ptrofs_eq_e: forall i j, Ptrofs.eq i j = true -> i=j.
Proof. intros. pose proof (Ptrofs.eq_spec i j); rewrite H in H0; auto. Qed.

Lemma allp_andp1  {A}{ND: NatDed A}:  forall B (any: B) (p: B -> A) q, andp (allp p) q = (allp (fun x => andp (p x) q)).
Proof.
 intros. apply pred_ext.
 apply allp_right; intro x.
 apply andp_derives; auto. apply allp_left with x; auto.
 apply andp_right. apply allp_right; intro x. apply allp_left with x. apply andp_left1; auto.
 apply allp_left with any. apply andp_left2; auto.
Qed.

Lemma allp_andp2  {A}{ND: NatDed A}:  forall B (any: B) p (q: B -> A),
     andp p (allp q) = (allp (fun x => andp p (q x))).
Proof.
intros. rewrite andp_comm. rewrite allp_andp1; auto.
f_equal. extensionality x. rewrite andp_comm; auto.
Qed.

Local Open Scope logic.

Class listspec {cs: compspecs} (list_structid: ident) (list_link: ident) (token: share -> val -> mpred):=
  mk_listspec {
   list_fields: members;
   list_struct := Tstruct list_structid noattr;
   list_members_eq: list_fields = co_members (get_co list_structid);
   list_struct_complete_legal_cosu: complete_legal_cosu_type list_struct = true; (* TODO: maybe this line not useful? *)
   list_link_type: nested_field_type list_struct (StructField list_link :: nil) = Tpointer list_struct noattr;
   list_token := token
}.

Section LIST1.
Context {cs: compspecs}.
Context  {list_structid: ident} {list_link: ident} {list_token: share -> val -> mpred}.

Fixpoint all_but_link (f: members) : members :=
 match f with
 | nil => nil
 | cons it f' => if ident_eq (fst it) list_link
                               then f'
                               else cons it (all_but_link f')
 end.

Lemma list_link_size_in_range (ls: listspec list_structid list_link list_token):
  0 < sizeof (nested_field_type list_struct (StructField list_link :: nil)) < Ptrofs.modulus.
Proof.
  rewrite list_link_type.
  unfold sizeof, Ctypes.sizeof.
  destruct Archi.ptr64 eqn:Hp.
  rewrite Ptrofs.modulus_eq64 by auto; computable.
  rewrite Ptrofs.modulus_eq32 by auto; computable.
Qed.

Definition elemtype (ls: listspec list_structid list_link list_token) :=
  compact_prod
  (map (fun it => reptype (field_type (fst it) list_fields)) (all_but_link list_fields)).

Definition field_type'  (F: members) (it: ident * type) :=
   reptype (field_type (fst it) F).

Definition add_link_back' {F f: members}
  (v: compact_prod (map (field_type' F) (all_but_link f))) :
  compact_prod (map (field_type' F) f).
  induction f as [| it0 f].
  + exact tt.
  +  destruct f as [| it1 f0].
    - exact (default_val _).
    - change (all_but_link (it0 :: it1 :: f0))
       with (if ident_eq (fst it0) list_link
                               then it1::f0
                               else cons it0 (all_but_link (it1::f0)))
       in v.
       change (reptype (field_type (fst it0) F) * compact_prod (map (field_type' F) (it1::f0)))%type.
       destruct (ident_eq (fst it0) list_link).
       exact (default_val _, v).
       destruct (all_but_link (it1 :: f0)) eqn:?.
       simpl in Heqm.
       destruct (ident_eq (fst it1) list_link); [ | discriminate Heqm].
        subst f0.
        exact (v, default_val _).
        exact (fst v, IHf (snd v)).
Defined.

Definition add_link_back
 (F f : members)
  (v : compact_prod
         (map (fun it : ident * type => reptype (field_type (fst it) F))
            (all_but_link f)))
  : compact_prod (map (fun it => reptype (field_type (fst it) F)) f)
  :=
list_rect
  (fun f0 : list (ident * type) =>
   compact_prod (map (field_type' F) (all_but_link f0)) ->
   compact_prod (map (field_type' F) f0))
  (fun _ : compact_prod (map (field_type' F) (all_but_link nil)) => tt)
  (fun (it0 : ident * type) (f0 : list (ident * type))
     (IHf : compact_prod (map (field_type' F) (all_but_link f0)) ->
            compact_prod (map (field_type' F) f0))
     (v0 : compact_prod (map (field_type' F) (all_but_link (it0 :: f0)))) =>
   match
     f0 as l
     return
       (compact_prod (map (field_type' F) (all_but_link (it0 :: l))) ->
        (compact_prod (map (field_type' F) (all_but_link l)) ->
         compact_prod (map (field_type' F) l)) ->
        compact_prod (map (field_type' F) (it0 :: l)))
   with
   | nil =>
       fun
         (_ : compact_prod (map (field_type' F) (all_but_link (it0 :: nil))))
         (_ : compact_prod (map (field_type' F) (all_but_link nil)) ->
              compact_prod (map (field_type' F) nil)) =>
       default_val (field_type (fst it0) F)
   | it1 :: f1 =>
       fun
         (v1 : compact_prod
                 (map (field_type' F) (all_but_link (it0 :: it1 :: f1))))
         (IHf0 : compact_prod
                   (map (field_type' F) (all_but_link (it1 :: f1))) ->
                 compact_prod (map (field_type' F) (it1 :: f1))) =>
       (if ident_eq (fst it0) list_link as s0
         return
           (compact_prod
              (map (field_type' F)
                 (if s0 then it1 :: f1 else it0 :: all_but_link (it1 :: f1))) ->
            reptype (field_type (fst it0) F) *
            compact_prod (map (field_type' F) (it1 :: f1)))
        then
         fun v2 : compact_prod (map (field_type' F) (it1 :: f1)) =>
         (default_val (field_type (fst it0) F), v2)
        else
         fun
           v2 : compact_prod
                  (map (field_type' F) (it0 :: all_but_link (it1 :: f1))) =>
         match
           all_but_link (it1 :: f1) as l
           return
             (all_but_link (it1 :: f1) = l ->
              compact_prod (map (field_type' F) (it0 :: l)) ->
              (compact_prod (map (field_type' F) l) ->
               compact_prod (map (field_type' F) (it1 :: f1))) ->
              reptype (field_type (fst it0) F) *
              compact_prod (map (field_type' F) (it1 :: f1)))
         with
         | nil =>
             fun (Heqm0 : all_but_link (it1 :: f1) = nil)
               (v3 : compact_prod (map (field_type' F) (it0 :: nil)))
               (IHf1 : compact_prod (map (field_type' F) nil) ->
                       compact_prod (map (field_type' F) (it1 :: f1))) =>
             let s0 := ident_eq (fst it1) list_link in
             (if s0
               return
                 ((if s0 then f1 else it1 :: all_but_link f1) = nil ->
                  reptype (field_type (fst it0) F) *
                  compact_prod (map (field_type' F) (it1 :: f1)))
              then
               fun Heqm1 : f1 = nil =>
               eq_rect_r
                 (fun f2 : members =>
                  (compact_prod (map (field_type' F) nil) ->
                   compact_prod (map (field_type' F) (it1 :: f2))) ->
                  reptype (field_type (fst it0) F) *
                  compact_prod (map (field_type' F) (it1 :: f2)))
                 (fun
                    _ : compact_prod (map (field_type' F) nil) ->
                        compact_prod (map (field_type' F) (it1 :: nil)) =>
                  (v3, default_val (field_type (fst it1) F)))
                 Heqm1 IHf1
              else
               fun Heqm1 : it1 :: all_but_link f1 = nil =>
                 False_rect
                   (reptype (field_type (fst it0) F) *
                    compact_prod (map (field_type' F) (it1 :: f1)))
                 (eq_rect (it1 :: all_but_link f1)
                    (fun e : members =>
                     match e with
                     | nil => False
                     | _ :: _ => True
                     end) I nil Heqm1)) Heqm0
         | p :: m0 =>
             fun (_ : all_but_link (it1 :: f1) = p :: m0)
               (v3 : compact_prod (map (field_type' F) (it0 :: p :: m0)))
               (IHf1 : compact_prod (map (field_type' F) (p :: m0)) ->
                       compact_prod (map (field_type' F) (it1 :: f1))) =>
             (fst v3, IHf1 (snd v3))
         end eq_refl v2 IHf0) v1
   end v0 IHf) f v.

(*
Definition add_link_back {ls: listspec list_structid list_link} {f F: members}
  (v: compact_prod (map (fun it => reptype (field_type (fst it) F)) (all_but_link f))) :
  compact_prod (map (fun it => reptype (field_type (fst it) F)) f).
  unfold all_but_link in v.
  induction f as [| [i0 t0] f].
  + exact tt.
  + simpl in *; destruct f as [| [i1 t1] f0] eqn:?; [| destruct (ident_eq i0 list_link)].
    - exact (default_val _).
    - exact (default_val _, v).
    - fold (all_but_link ((i1, t1) :: f0)) in IHf, v.
      destruct (all_but_link ((i1, t1) :: f0)) eqn:?.
      * simpl in Heqm.
        if_tac in Heqm; [| congruence].
        subst f0.
        exact (v, default_val _).
      * exact (fst v, IHf (snd v)).
Defined.
*)

Definition list_data {ls: listspec list_structid list_link list_token} (v: elemtype ls): reptype list_struct.
  unfold list_struct.
  pose (add_link_back _ _ v: reptype_structlist _).
  rewrite list_members_eq in r.
  exact (@fold_reptype _ (Tstruct _ _) r).
Defined.

Definition list_cell' (ls: listspec list_structid list_link list_token) sh v p :=
  (field_at_ sh list_struct (StructField list_link :: nil) p) -* (data_at sh list_struct (list_data v) p).

Definition list_cell (ls: listspec list_structid list_link list_token) (sh: Share.t)
   (v: elemtype ls) (p: val) : mpred :=
   !! field_compatible list_struct nil p &&
   struct_pred (all_but_link list_fields)
              (fun it v => withspacer sh
                (field_offset cenv_cs (fst it) list_fields + sizeof (field_type (fst it) list_fields))
                (field_offset_next cenv_cs (fst it) list_fields (co_sizeof (get_co list_structid)))
                (at_offset (data_at_rec sh (field_type (fst it) list_fields) v) (field_offset cenv_cs (fst it) list_fields)))
     v p.

Lemma struct_pred_type_changable:
  forall m m' A F v v' p p',
  m=m' ->
  JMeq v v' ->
  (forall it v, F it v p = F it v p') ->
  @struct_pred m A F v p = @struct_pred m' A F v' p'.
Proof.
intros.
subst m'. apply JMeq_eq in H0. subst v'.
induction m. reflexivity.
destruct m.
destruct a; simpl.
apply H1.
rewrite !struct_pred_cons2.
f_equal.
auto.
apply IHm.
Qed.


End LIST1.

Module LsegGeneral.

Section LIST2.
Context {cs: compspecs}.
Context  {list_structid: ident} {list_link: ident} {list_token: share -> val -> mpred}.

Fixpoint lseg (ls: listspec list_structid list_link list_token) (dsh psh: share)
            (contents: list (val * elemtype ls)) (x z: val) : mpred :=
 match contents with
 | (p,h)::hs => !! (p=x /\ ~ptr_eq x z) &&
              EX y:val,  !! is_pointer_or_null y &&
              list_token dsh x * list_cell ls dsh h x
              * field_at psh list_struct (StructField list_link ::nil)
                  (valinject (nested_field_type list_struct (StructField list_link :: nil)) y) x
              * lseg ls dsh psh hs y z
 | nil => !! (ptr_eq x z) && emp
 end.

Lemma lseg_unfold (ls: listspec list_structid list_link list_token): forall dsh psh contents v1 v2,
    lseg ls dsh psh contents v1 v2 =
     match contents with
     | (p,h)::t => !! (p=v1 /\ ~ ptr_eq v1 v2) && EX tail: val,
                      !! is_pointer_or_null tail &&
                      list_token dsh v1 * list_cell ls dsh h v1
                      * field_at psh list_struct (StructField list_link :: nil)
                          (valinject (nested_field_type list_struct (StructField list_link :: nil)) tail) v1
                      * lseg ls dsh psh t tail v2
     | nil => !! (ptr_eq v1 v2) && emp
     end.
Proof.
 intros.
 destruct contents as [ | [? ?] ?]; simpl; auto.
Qed.

Lemma lseg_eq (ls: listspec list_structid list_link list_token):
  forall dsh psh l v ,
  is_pointer_or_null v ->
    lseg ls dsh psh l v v = !!(l=nil) && emp.
Proof.
intros.
rewrite (lseg_unfold ls dsh psh l v v).
destruct l.
f_equal. f_equal.
apply prop_ext; split; intro; auto.
unfold ptr_eq.
unfold is_pointer_or_null in H.
destruct Archi.ptr64 eqn:Hp;
destruct v; inv H; auto;
unfold Ptrofs.cmpu; rewrite Ptrofs.eq_true; auto.
destruct p.
apply pred_ext;
apply derives_extract_prop; intro.
destruct H0.
contradiction H1.
destruct v; inv H; try split; auto; apply Ptrofs.eq_true.
inv H0.
Qed.

Definition lseg_cons (ls: listspec list_structid list_link list_token) dsh psh (l: list (val * elemtype ls)) (x z: val) : mpred :=
        !! (~ ptr_eq x z) &&
       EX h:(elemtype ls), EX r:list (val * elemtype ls), EX y:val,
             !!(l=(x,h)::r  /\ is_pointer_or_null y) &&
             list_token dsh x * list_cell ls dsh h x *
             field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) y) x *
             lseg ls dsh psh r y z.

Lemma lseg_unroll (ls: listspec list_structid list_link list_token): forall dsh psh l x z ,
    lseg ls dsh psh l x z =
      (!! (ptr_eq x z) && !! (l=nil) && emp) || lseg_cons ls dsh psh l x z.
Proof.
intros.
rewrite lseg_unfold at 1.
apply pred_ext; destruct l.
apply derives_extract_prop; intros.
rewrite prop_true_andp by auto.
rewrite prop_true_andp by auto.
apply orp_right1; auto.
destruct p.
apply orp_right2.
unfold lseg_cons.
apply derives_extract_prop; intros.
destruct H.
apply exp_left; intro tail.
normalize.
apply exp_right with e. rewrite TT_andp.
apply exp_right with l.
apply exp_right with tail.
repeat rewrite sepcon_andp_prop'.
apply andp_right.
apply prop_right; split; auto.
subst.
auto.
subst. auto.
apply orp_left.
rewrite andp_assoc;
do 2 (apply derives_extract_prop; intro).
 rewrite prop_true_andp by auto. auto.
unfold lseg_cons.
apply derives_extract_prop; intros.
apply exp_left; intro h.
apply exp_left; intro r.
apply exp_left; intro y.
do 3 rewrite sepcon_andp_prop'.
apply derives_extract_prop; intros [? ?].
inv H0.
destruct p.
apply orp_left.
rewrite andp_assoc;
do 2 (apply derives_extract_prop; intro).
inv H0.
unfold lseg_cons.
apply derives_extract_prop; intros.
apply exp_left; intro h.
apply exp_left; intro r.
apply exp_left; intro y.
do 3 rewrite sepcon_andp_prop'.
apply derives_extract_prop; intros [? ?].
symmetry in H0; inv H0.
 rewrite prop_true_andp by auto.
apply exp_right with y.
normalize.
Qed.

Lemma lseg_unroll_nonempty1 (ls: listspec list_structid list_link list_token):
   forall p P dsh psh h tail v1 v2,
    ~ ptr_eq v1 v2 ->
    is_pointer_or_null p ->
    P |-- list_token dsh v1 * list_cell ls dsh h v1 *
             (field_at psh list_struct (StructField list_link :: nil)
                   (valinject (nested_field_type list_struct (StructField list_link :: nil)) p) v1 *
               lseg ls dsh psh tail p v2) ->
    P |-- lseg ls dsh psh ((v1,h)::tail) v1 v2.
Proof. intros. rewrite lseg_unroll. apply orp_right2. unfold lseg_cons.
  rewrite prop_true_andp by auto.
  apply exp_right with h. apply exp_right with tail. apply exp_right with p.
    rewrite prop_true_andp by auto.
 rewrite sepcon_assoc.
 eapply derives_trans; [ apply H1 | ].
 apply sepcon_derives; auto.
Qed.

Lemma lseg_neq (ls: listspec list_structid list_link list_token):
  forall dsh psh s v v2,
    ptr_neq v v2 ->
     lseg ls dsh psh s v v2 = lseg_cons ls dsh psh s v v2.
intros. rewrite lseg_unroll.
apply pred_ext. apply orp_left; auto.
rewrite andp_assoc.
do 2 (apply derives_extract_prop; intro).
congruence.
apply orp_right2. auto.
Qed.

Lemma lseg_nonnull (ls: listspec list_structid list_link list_token):
  forall dsh psh s v,
      typed_true (tptr list_struct) v ->
     lseg ls dsh psh s v nullval = lseg_cons ls dsh psh s v nullval.
Proof.
intros. unfold nullval.
apply lseg_neq.
destruct v; inv H; intuition; try congruence.
intro. apply ptr_eq_e in H.
destruct Archi.ptr64 eqn:Hp; inv H.
inv H1.
intro. simpl in H.
destruct Archi.ptr64; congruence.
Qed.

Lemma unfold_lseg_neq (ls: listspec list_structid list_link list_token):
   forall P Q1 Q R (v v2: val) dsh psh (s: list (val * elemtype ls)),
      PROPx P (LOCALx (Q1::Q) (SEPx (lseg ls dsh psh s v v2 :: R))) |--
                        !! (ptr_neq v v2) ->
      PROPx P (LOCALx (Q1::Q) (SEPx (lseg ls dsh psh s v v2 :: R))) |--
     EX hryp: elemtype ls * list (val * elemtype ls) * val * val,
      match hryp with (h,r,y,p) =>
       !! (s=(p,h)::r /\ is_pointer_or_null y) &&
       !! (p=v) &&
      PROPx P (LOCALx Q
        (SEPx (list_token dsh v :: list_cell ls dsh h v::
                  field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) y) v ::
                  lseg ls dsh psh r y v2 ::
                  R)))
        end.
Proof.
intros.
apply derives_trans with
(PROPx P (LOCALx (Q1::Q) (SEPx (lseg_cons ls dsh psh s v v2 :: R)))).
apply derives_trans with
(!! ptr_neq v v2 && PROPx P (LOCALx (Q1::Q) (SEPx (lseg ls dsh psh s v v2 :: R)))).
apply andp_right; auto.
intro rho; unfold PROPx,LOCALx,SEPx,local,tc_expr,tc_lvalue; unfold_lift; simpl.
unfold lift1; simpl.
 repeat (apply derives_extract_prop; intro).
 rewrite prop_true_andp by auto.
 rewrite prop_true_andp by auto.
apply sepcon_derives; auto.
rewrite lseg_neq; auto.
intro rho; unfold PROPx,LOCALx,SEPx,local,tc_expr,tc_lvalue,lift2,lift1,lift0; simpl.
 unfold_lift.
 unfold lseg_cons. simpl.
 apply derives_extract_prop; intro.
 apply derives_extract_prop; intros [? ?].
 rewrite sepcon_andp_prop'.
 apply derives_extract_prop; intro.
 rewrite exp_sepcon1; apply exp_left; intro h.
 rewrite exp_sepcon1; apply exp_left; intro r.
 rewrite exp_sepcon1; apply exp_left; intro y.
 repeat rewrite sepcon_andp_prop'.
 apply derives_extract_prop; intros [? ?].
 subst.
 apply exp_right with (h,r,y, v).
 repeat rewrite prop_true_andp by auto.
 repeat rewrite sepcon_assoc.
 auto.
Qed.

Lemma unfold_lseg_cons (ls: listspec list_structid list_link list_token):
   forall P Q1 Q R e dsh psh s,
      PROPx P (LOCALx (Q1::Q) (SEPx (lseg ls dsh psh s e nullval :: R))) |--
                        !! (typed_true (tptr list_struct) e) ->
      PROPx P (LOCALx (Q1::Q) (SEPx (lseg ls dsh psh s e nullval :: R))) |--
     EX hryp: elemtype ls * list (val * elemtype ls) * val * val,
      match hryp with (h,r,y,p) =>
       !! (s=(p,h)::r /\ is_pointer_or_null y) &&
       !! (p=e)&&
      PROPx P (LOCALx Q
        (SEPx (list_token dsh e :: list_cell ls dsh h e ::
                  field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) y) e ::
                  lseg ls dsh psh r y nullval ::
                  R)))
        end.
Proof.
intros. apply unfold_lseg_neq.
eapply derives_trans.
apply H. normalize.
unfold local. super_unfold_lift.
unfold nullval.
intro.
apply ptr_eq_e in H1. subst.
normalize.
Qed.

Lemma semax_lseg_neq (ls: listspec list_structid list_link list_token):
  forall (Espec: OracleKind)
      Delta P Q dsh psh s v v2 R c Post,
    ~ (ptr_eq v v2) ->
  (forall (h: elemtype ls) (r: list (val * elemtype ls)) (y: val),
    s=(v,h)::r -> is_pointer_or_null y ->
    semax Delta
        (PROPx P (LOCALx Q
        (SEPx (list_token dsh v :: list_cell ls dsh h v ::
                  field_at psh list_struct (StructField list_link :: nil)
                      (valinject (nested_field_type list_struct (StructField list_link :: nil)) y) v ::
                  lseg ls dsh psh r y v2 ::
                  R)))) c Post) ->
   semax Delta
       (PROPx P (LOCALx Q (SEPx (lseg ls dsh psh s v v2 :: R))))
       c Post.
Proof.
intros.
rewrite lseg_neq by auto.
unfold lseg_cons.
apply semax_pre0 with
 (EX h: elemtype ls, EX r: list (val * elemtype ls), EX y: val,
  !!(s = (v, h) :: r /\ is_pointer_or_null y) &&
    PROPx P (LOCALx Q (SEPx (list_token dsh v :: list_cell ls dsh h v ::
       field_at psh list_struct (StructField list_link :: nil)
                   (valinject
                      (nested_field_type list_struct
                         (StructField list_link :: nil)) y) v ::
        lseg ls dsh psh r y v2 :: R)))).
go_lowerx; entailer.
Exists h r y.
rewrite <- ?sepcon_assoc.
normalize.
  autorewrite with subst norm1 norm2; normalize.
Intros h r y.
apply semax_extract_prop; intros [? ?].
eapply H0; eauto.
Qed.


Lemma semax_lseg_nonnull (ls: listspec list_structid list_link list_token):
  forall (Espec: OracleKind)
      Delta P Q dsh psh s v R c Post,
   ENTAIL Delta, PROPx P (LOCALx Q
            (SEPx (lseg ls dsh psh s v nullval :: R))) |--
                        !!(typed_true (tptr list_struct) v)  ->
  (forall (h: elemtype ls) (r: list (val * elemtype ls)) (y: val),
    s=(v,h)::r -> is_pointer_or_null y ->
    semax Delta
        (PROPx P (LOCALx Q
        (SEPx (list_token dsh v :: list_cell ls dsh h v ::
                  field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) y) v ::
                  lseg ls dsh psh r y nullval ::
                  R)))) c Post) ->
   semax Delta
       (PROPx P (LOCALx Q (SEPx (lseg ls dsh psh s v nullval :: R))))
       c Post.
Proof.
intros.
assert_PROP (~ ptr_eq v nullval).
eapply derives_trans; [apply H |].
normalize.
apply semax_lseg_neq; auto.
Qed.

Lemma lseg_nil_eq (ls: listspec list_structid list_link list_token):
    forall dsh psh p q, lseg ls dsh psh nil p q = !! (ptr_eq p q) && emp.
Proof. intros.
 rewrite lseg_unroll.
 apply pred_ext.
 apply orp_left.
 rewrite andp_assoc.
 apply andp_derives; auto.
rewrite prop_true_andp by auto. auto.
 unfold lseg_cons. normalize. inv H0.
 apply orp_right1.  rewrite andp_assoc.
 rewrite (prop_true_andp (_ = _)) by auto. auto.
Qed.

Lemma lseg_cons_eq (ls: listspec list_structid list_link list_token):
     forall dsh psh h r x z ,
    lseg ls dsh psh (h::r) x z =
        !!(x = fst h /\ ~ ptr_eq x z) &&
         (EX  y : val,
          !!(is_pointer_or_null y) &&
   list_token dsh x * list_cell ls dsh (snd h) x * field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) y) x *
   lseg ls dsh psh r y z).
Proof.
 intros. rewrite lseg_unroll.
 apply pred_ext.
 apply orp_left.
 rewrite andp_assoc.
 apply derives_extract_prop; intro.
 apply derives_extract_prop; intro.
 inv H0.
 unfold lseg_cons.
 normalize.
 symmetry in H0; inv H0.
 apply exp_right with y. normalize.
  autorewrite with subst norm1 norm2; normalize.
 normalize. destruct h as [p h]. simpl in *.
 apply orp_right2.
 unfold lseg_cons.
 rewrite prop_true_andp by auto.
 apply exp_right with h. apply exp_right with r.  apply exp_right with y.
 normalize.
  autorewrite with subst norm1 norm2; normalize.
Qed.

Definition lseg_cons_right (ls: listspec list_structid list_link list_token)
           dsh psh (l: list (val * elemtype ls)) (x z: val) : mpred :=
        !! (~ ptr_eq x z) &&
       EX h:(elemtype ls), EX r:list (val * elemtype ls), EX y:val,
             !!(l=r++(y,h)::nil /\ is_pointer_or_null y)  &&
                       list_token dsh y * list_cell ls dsh h y *
             field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) z) y *
             lseg ls dsh psh r x y.

Lemma lseg_cons_right_neq (ls: listspec list_structid list_link list_token): forall dsh psh l x h y w z,
             sepalg.nonidentity psh ->
             list_token dsh y * list_cell ls dsh h y * field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) z) y *
             lseg ls dsh psh l x y * field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) w) z
   |--   lseg ls dsh psh (l++(y,h)::nil) x z * field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) w) z.
Proof.
intros. rename H into SH.
assert (SZ: 0 < sizeof (nested_field_type list_struct (DOT list_link))).
  unfold sizeof; rewrite list_link_type; simpl; destruct Archi.ptr64; computable.
rewrite (field_at_isptr _ _ _ _ z).
normalize.
revert x; induction l; simpl; intros.
*
normalize.
  autorewrite with subst norm1 norm2; normalize.
 apply exp_right with z.
 entailer!.
*
destruct a as [v el].
normalize.
apply exp_right with x0.
normalize.
rewrite <- ?sepcon_assoc.
  autorewrite with subst norm1 norm2; normalize.
specialize (IHl x0).
entailer.
pull_right (list_cell ls dsh el x).
apply sepcon_derives; auto.
pull_right (field_at psh list_struct (StructField list_link :: nil)
      (valinject
         (nested_field_type list_struct (StructField list_link :: nil)) x0)
      x).
pull_right (list_token dsh x).
apply sepcon_derives; auto.
apply sepcon_derives; auto.
Qed.

Lemma lseg_cons_right_null (ls: listspec list_structid list_link list_token): forall dsh psh l x h y,
             list_token dsh y * list_cell ls dsh h y * field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) nullval) y *
             lseg ls dsh psh l x y
   |--   lseg ls dsh psh (l++(y,h)::nil) x nullval.
Proof.
intros.
revert x; induction l; simpl; intros.
*
normalize.
  autorewrite with subst norm1 norm2; normalize.
apply exp_right with nullval.
apply andp_right.
apply not_prop_right; intro.
apply ptr_eq_e in H. subst y.
entailer!.
destruct H. contradiction H.
rewrite prop_true_andp by reflexivity.
rewrite prop_true_andp
  by (unfold nullval; destruct Archi.ptr64 eqn:Hp; simpl; auto).
normalize.
*
destruct a as [v el].
normalize.
apply exp_right with x0.
normalize.
  autorewrite with subst norm1 norm2; normalize.
specialize (IHl x0).
apply andp_right.
rewrite prop_and.
apply andp_right; [ | apply prop_right; auto].
apply not_prop_right; intro.
apply ptr_eq_e in H0. subst x.
entailer.
destruct H2; contradiction H2.
eapply derives_trans.
2: apply sepcon_derives; [ | eassumption]; apply derives_refl.
clear IHl.
cancel.
Qed.


Lemma lseg_cons_right_list (ls: listspec list_structid list_link list_token): forall dsh psh l l' x h y z,
    sepalg.nonidentity psh ->
             list_token dsh y * list_cell ls dsh h y
           * field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) z) y
           * lseg ls dsh psh l x y
           * lseg ls dsh psh l' z nullval
   |--   lseg ls dsh psh (l++(y,h)::nil) x z * lseg ls dsh psh l' z nullval.
Proof.
intros.
destruct l'.
rewrite lseg_nil_eq.
pose proof ptr_eq_nullval.
normalize.
apply lseg_cons_right_null.
rewrite lseg_cons_eq.
Intros u. Exists u. subst z.
rewrite <- ?sepcon_assoc.
rewrite !prop_true_andp by auto.
normalize.
apply sepcon_derives; auto.
pull_right (list_cell ls dsh (snd p) (fst p)).
pull_right (list_token dsh (fst p)).
apply sepcon_derives; auto.
apply sepcon_derives; auto.
apply lseg_cons_right_neq; auto.
Qed.


Lemma lseg_unroll_right (ls: listspec list_structid list_link list_token): forall sh sh' l x z ,
    lseg ls sh sh' l x z = (!! (ptr_eq x z) && !! (l=nil) && emp) || lseg_cons_right ls sh sh' l x z.
Abort.  (* not likely true *)


Lemma lseg_local_facts:
  forall ls dsh psh contents p q,
     lseg ls dsh psh contents p q |--
     !! (is_pointer_or_null p /\ (p=q <-> contents=nil)).
Proof.
intros.
rewrite lseg_unfold.
destruct contents.
apply derives_extract_prop; intro.
unfold ptr_eq in H.
apply prop_right.
destruct p; try contradiction; simpl; auto.
destruct q; try contradiction; auto.
unfold Int.cmpu in H.
destruct H as [? [? ?]].
apply int_eq_e in H0.
apply int_eq_e in H1. subst. rewrite H.
split; auto; split; auto.
destruct q; try contradiction; auto.
unfold Int64.cmpu in H.
destruct H as [? [? ?]].
apply int64_eq_e in H0.
apply int64_eq_e in H1. subst. rewrite H.
split3; auto.
destruct q; try contradiction.
destruct H; subst.
unfold Ptrofs.cmpu in H0.
apply ptrofs_eq_e in H0.
subst. tauto.
destruct p0.
normalize.
rewrite field_at_isptr.
normalize.
  autorewrite with subst norm1 norm2; normalize.
apply prop_right.
split. intro; subst q.
contradiction H. normalize.
intros. discriminate.
Qed.

Definition lseg_cell  (ls: listspec list_structid list_link list_token)
    (dsh psh : share)
    (v: elemtype ls) (x y: val) :=
   !!is_pointer_or_null y && list_token dsh x * list_cell ls dsh v x * field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) y) x.

Lemma lseg_cons_eq2: forall
  (ls : listspec list_structid list_link list_token) (dsh psh : share) (h : elemtype ls)
   (r : list (val * elemtype ls))
  (x x' z : val), lseg ls dsh psh ((x',h) :: r) x z =
  !!(x=x' /\ ~ ptr_eq x z) && (EX  y : val, lseg_cell ls dsh psh h x y * lseg ls dsh psh r y z).
Proof.
  intros.
  rewrite -> lseg_cons_eq.
  unfold lseg_cell.
 normalize.
Qed.

Lemma list_append: forall {dsh psh: share}
  {ls : listspec list_structid list_link list_token} (hd mid tl:val) ct1 ct2 P,
  (forall x tl', lseg_cell ls dsh psh x tl tl' * P tl |-- FF) ->
  (lseg ls dsh psh ct1 hd mid) * lseg ls dsh psh ct2 mid tl * P tl|--
  (lseg ls dsh psh (ct1 ++ ct2) hd tl) * P tl.
Proof.
  intros.
  revert hd; induction ct1; simpl; intros; auto.
  *
  normalize.
  *
  destruct a  as [v a].
  normalize.
  autorewrite with subst norm1 norm2; normalize.
  apply exp_right with y.
  apply andp_right.
  apply not_prop_right; intro. apply ptr_eq_e in H1; subst hd.
  clear IHct1.
  unfold lseg_cell in H.
  specialize (H a y).
  rewrite prop_true_andp in H by auto.
  apply derives_trans with
        (lseg ls dsh psh ct1 y mid * lseg ls dsh psh ct2 mid tl * FF).
 cancel. auto.
  rewrite sepcon_FF; auto.
  normalize.
  specialize (IHct1 y). clear H.
   do 2 rewrite sepcon_assoc.
  eapply derives_trans.
 apply sepcon_derives.
  apply derives_refl.
  rewrite <- !sepcon_assoc; eassumption.
  cancel.
Qed.

Lemma list_append_null:
  forall
   (ls: listspec list_structid list_link list_token)
   (dsh psh: share)
   (hd mid: val) ct1 ct2,
   lseg ls dsh psh ct1 hd mid * lseg ls dsh psh ct2 mid nullval |--
   lseg ls dsh psh (ct1++ct2) hd nullval.
Proof.
intros.
 rewrite <- sepcon_emp.
 eapply derives_trans; [ | apply (list_append hd mid nullval ct1 ct2 (fun _ => emp))].
 normalize.
 intros.
  unfold lseg_cell. simpl. saturate_local. destruct H. contradiction H.
Qed.


End LIST2.

Hint Rewrite @lseg_nil_eq : norm.

Hint Rewrite @lseg_eq using reflexivity: norm.

#[export] Hint Resolve lseg_local_facts : saturate_local.
End LsegGeneral.

Module LsegSpecial.

Section LIST.
Context {cs: compspecs}.
Context  {list_structid: ident} {list_link: ident} {list_token: share -> val -> mpred}.

Definition lseg (ls: listspec list_structid list_link list_token) (sh: share)
   (contents: list (elemtype ls)) (x y: val) : mpred :=
    EX al:list (val*elemtype ls),
          !! (contents = map snd al) &&
             LsegGeneral.lseg ls sh sh al x y.

Lemma lseg_unfold (ls: listspec list_structid list_link list_token): forall sh contents v1 v2,
    lseg ls sh contents v1 v2 =
     match contents with
     | h::t => !! (~ ptr_eq v1 v2) && EX tail: val,
                      !! is_pointer_or_null tail &&
                      list_token sh v1 * list_cell ls sh h v1
                      * field_at sh list_struct (StructField list_link :: nil)
                          (valinject (nested_field_type list_struct (StructField list_link :: nil)) tail) v1
                      *  lseg ls sh t tail v2
     | nil => !! (ptr_eq v1 v2) && emp
     end.
Proof.
 intros.
 unfold lseg.
 revert v1; induction contents; intros.
 apply pred_ext.
 normalize. destruct al; inv H.
 rewrite LsegGeneral.lseg_nil_eq; auto.
 apply exp_right with nil.
 apply derives_extract_prop; intro.
 normalize.
 apply pred_ext.
 apply exp_left; intros [ | [v1' a'] al].
 normalize. inv H.
 apply derives_extract_prop; intro.
 symmetry in H; inv H.
 rewrite LsegGeneral.lseg_cons_eq; auto.
 apply derives_extract_prop; intros [? ?].
 simpl in H;  subst v1'.
 apply exp_left; intro y.
 normalize. apply exp_right with y. normalize.
 repeat apply sepcon_derives; auto.
 apply exp_right with al; normalize.
 normalize.
 apply exp_right with ((v1,a)::al); normalize.
 simpl.
 normalize. apply exp_right with tail. normalize.
  autorewrite with subst norm1 norm2; normalize.
Qed.

Lemma lseg_eq (ls: listspec list_structid list_link list_token):
  forall sh l v ,
  is_pointer_or_null v ->
    lseg ls sh l v v = !!(l=nil) && emp.
Proof.
intros.
unfold lseg.
apply pred_ext.
normalize.
rewrite LsegGeneral.lseg_eq by auto. normalize.
apply exp_right with nil.
normalize.
Qed.

Definition lseg_cons (ls: listspec list_structid list_link list_token) sh (l: list (elemtype ls)) (x z: val) : mpred :=
        !! (~ ptr_eq x z) &&
       EX h:(elemtype ls), EX r:list (elemtype ls), EX y:val,
             !!(l=h::r  /\ is_pointer_or_null y) &&
             list_token sh x * list_cell ls sh h x *
             field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) y) x *
              lseg ls sh r y z.

Lemma lseg_unroll (ls: listspec list_structid list_link list_token): forall sh l x z ,
    lseg ls sh l x z =
      (!! (ptr_eq x z) && !! (l=nil) && emp) || lseg_cons ls sh l x z.
Proof.
intros.
unfold lseg, lseg_cons.
apply pred_ext.
*
apply exp_left; intros.
apply derives_extract_prop; intro.
rewrite LsegGeneral.lseg_unroll.
apply orp_left; [apply orp_right1 | apply orp_right2].
rewrite andp_assoc; repeat (apply derives_extract_prop; intro).
subst. simpl.
normalize.
unfold LsegGeneral.lseg_cons.
apply derives_extract_prop; intro.
rewrite prop_true_andp by auto.
apply exp_derives; intro h.
apply exp_left; intro r; apply exp_right with (map snd r).
apply exp_derives; intro y.
normalize.
subst l.
unfold lseg.
cancel.
apply exp_right with r; normalize.
*
apply orp_left.
rewrite andp_assoc; repeat (apply derives_extract_prop; intro).
subst.
apply exp_right with nil.
simpl. normalize.
  autorewrite with subst norm1 norm2; normalize.
apply derives_extract_prop; intro.
apply exp_left; intro h.
apply exp_left; intro r.
apply exp_left; intro y.
normalize.
unfold lseg.
normalize.
apply exp_right with ((x,h)::al).
normalize.
simpl.
normalize.
apply exp_right with y.
normalize.
  autorewrite with subst norm1 norm2; normalize.
Qed.

Lemma lseg_unroll_nonempty1 (ls: listspec list_structid list_link list_token):
   forall p P sh h (tail: list (elemtype ls)) v1 v2,
    ~ ptr_eq v1 v2 ->
    is_pointer_or_null p ->
    P |-- list_token sh v1 * list_cell ls sh h v1 *
             (field_at sh list_struct (StructField list_link :: nil)
                   (valinject (nested_field_type list_struct (StructField list_link :: nil)) p) v1 *
               lseg ls sh tail p v2) ->
    P |-- lseg ls sh (h::tail) v1 v2.
Proof. intros. rewrite lseg_unroll. apply orp_right2. unfold lseg_cons.
  rewrite prop_true_andp by auto.
  apply exp_right with h. apply exp_right with tail. apply exp_right with p.
    rewrite prop_true_andp by auto.
 rewrite sepcon_assoc.
 eapply derives_trans; [ apply H1 | ].
 apply sepcon_derives; auto.
Qed.

Lemma lseg_neq (ls: listspec list_structid list_link list_token):
  forall sh s v v2,
    ptr_neq v v2 ->
     lseg ls sh s v v2 = lseg_cons ls sh s v v2.
intros. rewrite lseg_unroll.
apply pred_ext. apply orp_left; auto.
rewrite andp_assoc.
do 2 (apply derives_extract_prop; intro).
congruence.
apply orp_right2. auto.
Qed.

Lemma lseg_nonnull (ls: listspec list_structid list_link list_token):
  forall sh s v,
      typed_true (tptr list_struct) v ->
     lseg ls sh s v nullval = lseg_cons ls sh s v nullval.
Proof.
intros. unfold nullval.
apply lseg_neq.
unfold typed_true, strict_bool_val in H.
simpl in H.
destruct Archi.ptr64 eqn:Hp.
*
destruct v; inv H. 
destruct (Int64.eq i Int64.zero); inv H1.
intro; apply ptr_eq_e in H; inv H.
*
destruct v; inv H.
destruct (Int.eq i Int.zero); inv H1.
intro; apply ptr_eq_e in H; inv H.
Qed.

Lemma unfold_lseg_neq (ls: listspec list_structid list_link list_token):
   forall P Q1 Q R (v v2: val) sh (s: list (elemtype ls)),
      PROPx P (LOCALx (Q1::Q) (SEPx (lseg ls sh s v v2 :: R))) |--
                        !! (ptr_neq v v2) ->
      PROPx P (LOCALx (Q1::Q) (SEPx (lseg ls sh s v v2 :: R))) |--
     EX hryp: elemtype ls * list (elemtype ls) * val,
      match hryp with (h,r,y) =>
       !! (s=h::r /\ is_pointer_or_null y) &&
      PROPx P (LOCALx Q
        (SEPx (list_token sh v :: list_cell ls sh h v::
                  field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) y) v ::
                   lseg ls sh r y v2 ::
                  R)))
        end.
Proof.
intros.
apply derives_trans with
(PROPx P (LOCALx (Q1::Q) (SEPx (lseg_cons ls sh s v v2 :: R)))).
apply derives_trans with
(!! (ptr_neq v v2) && PROPx P (LOCALx (Q1::Q) (SEPx (lseg ls sh s v v2 :: R)))).
apply andp_right; auto.
intro rho; unfold PROPx,LOCALx,SEPx,local,tc_expr,tc_lvalue; unfold_lift; simpl.
unfold lift1; simpl.
 repeat (apply derives_extract_prop; intro).
 rewrite prop_true_andp by auto.
 rewrite prop_true_andp by auto.
apply sepcon_derives; auto.
rewrite lseg_neq; auto.
intro rho; unfold PROPx,LOCALx,SEPx,local,tc_expr,tc_lvalue,lift2,lift1,lift0; simpl.
 unfold_lift.
 unfold lseg_cons. simpl.
 apply derives_extract_prop; intro.
 apply derives_extract_prop; intros [? ?].
 rewrite sepcon_andp_prop'.
 apply derives_extract_prop; intro.
 rewrite exp_sepcon1; apply exp_left; intro h.
 rewrite exp_sepcon1; apply exp_left; intro r.
 rewrite exp_sepcon1; apply exp_left; intro y.
 repeat rewrite sepcon_andp_prop'.
 apply derives_extract_prop; intros [? ?].
 subst.
 apply exp_right with (h,r,y).
 repeat rewrite prop_true_andp by auto.
 repeat rewrite sepcon_assoc.
 auto.
Qed.

Lemma unfold_lseg_cons (ls: listspec list_structid list_link list_token):
   forall P Q1 Q R e sh s,
      PROPx P (LOCALx (Q1::Q) (SEPx (lseg ls sh s e nullval :: R))) |--
                        !!(typed_true (tptr list_struct) e) ->
      PROPx P (LOCALx (Q1::Q) (SEPx (lseg ls sh s e nullval :: R))) |--
     EX hryp: elemtype ls * list (elemtype ls) * val,
      match hryp with (h,r,y) =>
       !! (s=h::r /\ is_pointer_or_null y) &&
      PROPx P (LOCALx Q
        (SEPx (list_token sh e :: list_cell ls sh h e ::
                  field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) y) e ::
                   lseg ls sh r y nullval ::
                  R)))
        end.
Proof.
intros. apply unfold_lseg_neq.
eapply derives_trans.
apply H. normalize.
unfold local. super_unfold_lift.
unfold nullval.
destruct e; inv H0; try congruence; auto.
intro. apply ptr_eq_e in H0.
destruct Archi.ptr64; inv H0.
Qed.

Lemma semax_lseg_neq (ls: listspec list_structid list_link list_token):
  forall (Espec: OracleKind)
      Delta P Q sh s v v2 R c Post,
    ~ (ptr_eq v v2) ->
  (forall (h: elemtype ls) (r: list (elemtype ls)) (y: val),
    s=h::r -> is_pointer_or_null y ->
    semax Delta
        (PROPx P (LOCALx Q
        (SEPx (list_token sh v :: list_cell ls sh h v ::
                  field_at sh list_struct (StructField list_link :: nil)
                      (valinject (nested_field_type list_struct (StructField list_link :: nil)) y) v ::
                   lseg ls sh r y v2 ::
                  R)))) c Post) ->
   semax Delta
       (PROPx P (LOCALx Q (SEPx (lseg ls sh s v v2 :: R))))
       c Post.
Proof.
intros.
rewrite lseg_neq by auto.
unfold lseg_cons.
apply semax_pre0 with
 (EX h: elemtype ls, EX r: list (elemtype ls), EX y: val,
  !!(s = h :: r /\ is_pointer_or_null y) &&
    PROPx P (LOCALx Q (SEPx (list_token sh v :: list_cell ls sh h v ::
       field_at sh list_struct (StructField list_link :: nil)
                   (valinject
                      (nested_field_type list_struct
                         (StructField list_link :: nil)) y) v ::
        lseg ls sh r y v2 :: R)))).
go_lowerx; entailer.  (* Intros h r y should work here, but doesn't. *)
Exists h r y.
rewrite <- ?sepcon_assoc.
normalize.
  autorewrite with subst norm1 norm2; normalize.
Intros h r y.
apply semax_extract_prop; intros [? ?].
eapply H0; eauto.
Qed.


Lemma semax_lseg_nonnull (ls: listspec list_structid list_link list_token):
  forall (Espec: OracleKind)
      Delta P Q sh s v R c Post,
      ENTAIL Delta, PROPx P (LOCALx Q
            (SEPx (lseg ls sh s v nullval :: R))) |--
                        !!(typed_true (tptr list_struct) v)  ->
  (forall (h: elemtype ls) (r: list (elemtype ls)) (y: val),
    s=h::r -> is_pointer_or_null y ->
    semax Delta
        (PROPx P (LOCALx Q
        (SEPx (list_token sh v :: list_cell ls sh h v ::
                  field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) y) v ::
                   lseg ls sh r y nullval ::
                  R)))) c Post) ->
   semax Delta
       (PROPx P (LOCALx Q (SEPx (lseg ls sh s v nullval :: R))))
       c Post.
Proof.
intros.
assert_PROP (~ ptr_eq v nullval).
eapply derives_trans; [apply H |].
normalize.
apply semax_lseg_neq; auto.
Qed.

Lemma lseg_nil_eq (ls: listspec list_structid list_link list_token):
    forall sh p q, lseg ls sh nil p q = !! (ptr_eq p q) && emp.
Proof. intros.
 rewrite lseg_unroll.
 apply pred_ext.
 apply orp_left.
 rewrite andp_assoc.
 apply andp_derives; auto.
rewrite prop_true_andp by auto. auto.
 unfold lseg_cons. normalize. inv H0.
 apply orp_right1.  rewrite andp_assoc.
 rewrite (prop_true_andp (_ = _)) by auto. auto.
Qed.

Lemma lseg_cons_eq (ls: listspec list_structid list_link list_token):
     forall sh h r x z ,
    lseg ls sh (h::r) x z =
        !!(~ ptr_eq x z) &&
         (EX  y : val,
          !!(is_pointer_or_null y) &&
   list_token sh x * list_cell ls sh h x * field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) y) x *
   lseg ls sh r y z).
Proof.
 intros. rewrite lseg_unroll.
 apply pred_ext.
 apply orp_left.
 rewrite andp_assoc.
 apply derives_extract_prop; intro.
 apply derives_extract_prop; intro.
 inv H0.
 unfold lseg_cons.
 normalize.
 symmetry in H0; inv H0.
 apply exp_right with y. normalize.
 apply orp_right2.
 unfold lseg_cons.
 apply andp_derives; auto.
 apply exp_right with h. apply exp_right with r.  apply exp_derives; intro y.
 normalize.
  autorewrite with subst norm1 norm2; normalize.
Qed.

Definition lseg_cons_right (ls: listspec list_structid list_link list_token)
           sh (l: list (elemtype ls)) (x z: val) : mpred :=
        !! (~ ptr_eq x z) &&
       EX h:(elemtype ls), EX r:list (elemtype ls), EX y:val,
             !!(l=r++(h::nil) /\ is_pointer_or_null y)  &&
                       list_token sh y * list_cell ls sh h y *
             field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) z) y *
              lseg ls sh r x y.

Lemma lseg_cons_right_neq (ls: listspec list_structid list_link list_token): forall sh l x h y w z,
       sepalg.nonidentity sh ->
             list_token sh y * list_cell ls sh h y * field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) z) y *
             lseg ls sh l x y * field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) w) z
   |--   lseg ls sh (l++h::nil) x z * field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) w) z.
Proof.
intros.
unfold lseg.
normalize.
apply exp_right with (al ++ (y,h)::nil).
rewrite prop_true_andp by (rewrite map_app; reflexivity).
eapply derives_trans; [ | apply LsegGeneral.lseg_cons_right_neq; auto].
cancel.
Qed.

Lemma lseg_cons_right_null (ls: listspec list_structid list_link list_token): forall sh l x h y,
             list_token sh y * list_cell ls sh h y * field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) nullval) y *
             lseg ls sh l x y
   |--   lseg ls sh (l++h::nil) x nullval.
Proof.
intros.
unfold lseg.
normalize.
apply exp_right with (al ++ (y,h)::nil).
rewrite prop_true_andp by (rewrite map_app; reflexivity).
eapply derives_trans; [ | apply LsegGeneral.lseg_cons_right_null].
cancel.
Qed.


Lemma lseg_cons_right_list (ls: listspec list_structid list_link list_token): forall sh l l' x h y z,
              sepalg.nonidentity sh ->
             list_token sh y * list_cell ls sh h y * field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) z) y *
             lseg ls sh l x y * lseg ls sh l' z nullval
   |--   lseg ls sh (l++h::nil) x z * lseg ls sh l' z nullval.
Proof.
intros.
destruct l'.
rewrite lseg_nil_eq.
pose proof ptr_eq_nullval.
normalize.
apply lseg_cons_right_null.
rewrite lseg_cons_eq.
Intros u.
Exists u.
rewrite !prop_true_andp by auto.
rewrite <- !sepcon_assoc.
apply sepcon_derives; auto.
pull_right (list_cell ls sh e z).
pull_right (list_token sh z).
apply sepcon_derives; auto.
apply sepcon_derives; auto.
apply lseg_cons_right_neq.
auto.
Qed.

Lemma lseg_unroll_right (ls: listspec list_structid list_link list_token): forall sh l x z ,
    lseg ls sh l x z = (!! (ptr_eq x z) && !! (l=nil) && emp) || lseg_cons_right ls sh l x z.
Abort.  (* not likely true *)

Lemma lseg_local_facts:
  forall ls sh contents p q,
     lseg ls sh contents p q |--
     !! (is_pointer_or_null p /\ (p=q <-> contents=nil)).
Proof.
intros.
unfold lseg.
normalize.
eapply derives_trans; [apply LsegGeneral.lseg_local_facts |].
normalize.
split; auto.
rewrite H.
clear.
destruct al; simpl; intuition; try congruence.
Qed.

Definition lseg_cell (ls: listspec list_structid list_link list_token)
    (sh : share)
    (v: elemtype ls) (x y: val) :=
   !!is_pointer_or_null y && list_token sh x * list_cell ls sh v x * field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) y) x.

Lemma lseg_cons_eq2: forall
  (ls : listspec list_structid list_link list_token) (sh : share) (h : elemtype ls)
   (r : list (elemtype ls))
  (x z : val), lseg ls sh (h :: r) x z =
  !!(~ ptr_eq x z) && (EX  y : val, lseg_cell ls sh h x y * lseg ls sh r y z).
Proof.
  intros.
  rewrite -> lseg_cons_eq.
  unfold lseg_cell.
 normalize.
Qed.

Lemma list_append: forall {sh: share}
  {ls : listspec list_structid list_link list_token} (hd mid tl:val) ct1 ct2 P,
  (forall x tl', lseg_cell ls sh x tl tl' * P tl |-- FF) ->
  (lseg ls sh ct1 hd mid) * lseg ls sh ct2 mid tl * P tl|--
  (lseg ls sh (ct1 ++ ct2) hd tl) * P tl.
Proof.
  intros.
  unfold lseg.
 normalize.
 eapply derives_trans.
 apply LsegGeneral.list_append.
 intros.
 eapply derives_trans; [ | apply (H x0 tl')].
 unfold lseg_cell, LsegGeneral.lseg_cell.
 entailer.
 apply exp_right with (x++al).
 rewrite prop_true_andp; auto.
 rewrite map_app; reflexivity.
Qed.

Lemma list_append_null:
  forall
   (ls: listspec list_structid list_link list_token)
   (sh: share)
   (hd mid: val) ct1 ct2,
   lseg ls sh ct1 hd mid * lseg ls sh ct2 mid nullval |--
   lseg ls sh (ct1++ct2) hd nullval.
Proof.
intros.
 rewrite <- sepcon_emp.
 eapply derives_trans; [ | apply (list_append hd mid nullval ct1 ct2 (fun _ => emp))].
 normalize.
 intros.
  unfold lseg_cell. simpl. saturate_local. destruct H. contradiction H.
Qed.

(*
Lemma lseg_valid_pointer:
  forall (ls : listspec list_structid list_link list_token) sh contents p q R,
   sepalg.nonidentity sh ->
   field_offset cenv_cs list_link list_fields + sizeof (field_type list_link list_fields)
   = field_offset_next cenv_cs list_link list_fields  (co_sizeof (get_co list_structid)) ->
    R |-- valid_pointer q ->
    R * lseg ls sh contents p q |-- valid_pointer p.
Proof.
intros ? ? ? ? ? ? NON_ID ? ?.
destruct contents.
rewrite lseg_nil_eq. normalize.
unfold lseg; simpl.
normalize.
destruct al; inv H1.
rewrite LsegGeneral.lseg_cons_eq.
normalize.
destruct p0 as [p z]; simpl in *.
apply sepcon_valid_pointer2.
apply sepcon_valid_pointer1.
rewrite sepcon_assoc.
apply sepcon_valid_pointer2.
eapply derives_trans.
apply sepcon_derives ; [ apply derives_refl | ]. cancel.
admit.
Admitted.
*)

End LIST.

Hint Rewrite @lseg_nil_eq : norm.
Hint Rewrite @lseg_eq using reflexivity: norm.
#[export] Hint Resolve lseg_local_facts : saturate_local.

Lemma list_cell_local_facts:
  forall {cs: compspecs} {list_structid list_link: ident}{list_token}
    (ls: listspec list_structid list_link list_token) sh v p,
   list_cell ls sh v p |-- !! field_compatible list_struct nil p.
Proof.
intros.
unfold list_cell.
normalize.
Qed.
#[export] Hint Resolve list_cell_local_facts : saturate_local.

End LsegSpecial.

Module Links.

Section LIST2.
Context {cs: compspecs}.
Context  {list_structid: ident} {list_link: ident}{list_token: share -> val -> mpred}.

Definition vund  (ls: listspec list_structid list_link list_token) : elemtype ls :=
 compact_prod_gen
      (fun it => default_val (field_type (fst it) list_fields)) (@all_but_link list_link  list_fields).

Definition lseg (ls: listspec list_structid list_link list_token) (dsh psh: share)
            (contents: list val) (x z: val) : mpred :=
  LsegGeneral.lseg ls dsh psh (map (fun v => (v, vund ls)) contents) x z.

Lemma lseg_unfold (ls: listspec list_structid list_link list_token): forall dsh psh contents v1 v2,
    lseg ls dsh psh contents v1 v2 =
     match contents with
     | p::t => !! (p=v1 /\ ~ ptr_eq v1 v2) && EX tail: val,
                      !! is_pointer_or_null tail &&
                      list_token dsh v1 * list_cell ls dsh (vund ls) v1
                      * field_at psh list_struct (StructField list_link :: nil)
                          (valinject (nested_field_type list_struct (StructField list_link :: nil)) tail) v1
                      * lseg ls dsh psh t tail v2
     | nil => !! (ptr_eq v1 v2) && emp
     end.
Proof.
 intros.
 unfold lseg.
 rewrite LsegGeneral.lseg_unfold.
 revert v1; induction contents; simpl; intros; auto.
Qed.

Lemma lseg_eq (ls: listspec list_structid list_link list_token):
  forall dsh psh l v ,
  is_pointer_or_null v ->
    lseg ls dsh psh l v v = !!(l=nil) && emp.
Proof.
intros.
rewrite (lseg_unfold ls dsh psh l v v).
destruct l.
f_equal. f_equal.
apply prop_ext; split; intro; auto.
normalize.
apply pred_ext;
apply derives_extract_prop; intro.
destruct H0.
contradiction H1.
destruct v; inv H; try split; auto.
unfold Ptrofs.cmpu. apply Ptrofs.eq_true.
inv H0.
Qed.

Definition lseg_cons (ls: listspec list_structid list_link list_token) dsh psh
           (l: list val) (x z: val) : mpred :=
        !! (~ ptr_eq x z) &&
       EX h:(elemtype ls), EX r:list val, EX y:val,
             !!(l=x::r  /\ is_pointer_or_null y) &&
             list_token dsh x * list_cell ls dsh h x *
             field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) y) x *
             lseg ls dsh psh r y z.

Lemma lseg_nil_eq (ls: listspec list_structid list_link list_token):
    forall dsh psh p q,
   lseg ls dsh psh nil p q = !! (ptr_eq p q) && emp.
Proof. intros.
 reflexivity.
Qed.

Definition lseg_cons_right (ls: listspec list_structid list_link list_token)
           dsh psh (l: list val) (x z: val) : mpred :=
        !! (~ ptr_eq x z) &&
       EX r:list val , EX y:val,
             !!(l=r++y::nil /\ is_pointer_or_null y)  &&
                       list_cell ls dsh (vund ls) y *
             field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) z) y *
             lseg ls dsh psh r x y.

Lemma lseg_unroll_right (ls: listspec list_structid list_link list_token): forall sh sh' l x z ,
    lseg ls sh sh' l x z = (!! (ptr_eq x z) && !! (l=nil) && emp) || lseg_cons_right ls sh sh' l x z.
Abort.  (* not likely true *)

Lemma lseg_local_facts:
  forall ls dsh psh contents p q,
     lseg ls dsh psh contents p q |--
     !! (is_pointer_or_null p /\ (p=q <-> contents=nil)).
Proof.
intros.
rewrite lseg_unfold.
destruct contents.
apply derives_extract_prop; intro.
unfold ptr_eq in H.
apply prop_right.
destruct p; try contradiction; simpl; auto.
destruct q; try contradiction; auto.
destruct H as [? [? ?]]. rewrite H.
unfold Int.cmpu in *.
apply int_eq_e in H0.
apply int_eq_e in H1. subst.
split; auto; split; auto.
destruct q; try contradiction; auto.
destruct H as [? [? ?]]. rewrite H.
unfold Int64.cmpu in *.
apply int64_eq_e in H0.
apply int64_eq_e in H1. subst.
split; auto; split; auto.
destruct q; try contradiction; auto.
destruct H; subst.
unfold Ptrofs.cmpu in *.
apply ptrofs_eq_e in H0. subst.
intuition.
normalize.
rewrite field_at_isptr.
normalize.
  autorewrite with subst norm1 norm2; normalize.
apply prop_right.
split. intro; subst q.
contradiction H. normalize.
intros. discriminate.
Qed.

Definition lseg_cell  (ls: listspec list_structid list_link list_token)
    (dsh psh : share)
    (v: elemtype ls) (x y: val) :=
   !!is_pointer_or_null y && list_token dsh x * list_cell ls dsh v x * field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) y) x.

Lemma list_append: forall {dsh psh: share}
  {ls : listspec list_structid list_link list_token} (hd mid tl:val) ct1 ct2 P,
  (forall tl', lseg_cell ls dsh psh (vund ls) tl tl' * P tl |-- FF) ->
  (lseg ls dsh psh ct1 hd mid) * lseg ls dsh psh ct2 mid tl * P tl|--
  (lseg ls dsh psh (ct1 ++ ct2) hd tl) * P tl.
Proof.
 intros.
 unfold lseg.
 revert hd; induction ct1; simpl; intros; auto.
*
 normalize.
*
 normalize.
 progress (autorewrite with subst norm1 norm2); normalize.
 apply exp_right with y.
 apply andp_right.
 +
  apply not_prop_right; intro. apply ptr_eq_e in H1; subst hd.
  clear IHct1.
  specialize (H y).
  unfold lseg_cell in H.
  rewrite prop_true_andp in H by auto.
  change (LsegGeneral.lseg ls dsh psh (map (fun v : val => (v, vund ls)) ct1))
    with (lseg ls dsh psh ct1).
  change (LsegGeneral.lseg ls dsh psh (map (fun v : val => (v, vund ls)) ct2))
    with (lseg ls dsh psh ct2).
  apply derives_trans with
        (lseg ls dsh psh ct1 y mid * lseg ls dsh psh ct2 mid tl * FF).
  cancel. auto.
  rewrite sepcon_FF; auto.
 +
  normalize.
  specialize (IHct1 y). clear H.
   do 2 rewrite sepcon_assoc.
  eapply derives_trans.
 apply sepcon_derives.
  apply derives_refl.
  rewrite <- !sepcon_assoc; eassumption.
  cancel.
Qed.

Lemma list_append_null:
  forall
   (ls: listspec list_structid list_link list_token)
   (dsh psh: share)
   (hd mid: val) ct1 ct2,
   lseg ls dsh psh ct1 hd mid * lseg ls dsh psh ct2 mid nullval |--
   lseg ls dsh psh (ct1++ct2) hd nullval.
Proof.
intros.
 rewrite <- sepcon_emp.
 eapply derives_trans; [ | apply (list_append hd mid nullval ct1 ct2 (fun _ => emp))].
 normalize.
 intros.
  unfold lseg_cell. simpl. saturate_local. destruct H. contradiction H.
Qed.

Lemma list_cell_valid_pointerx:
  forall (ls : listspec list_structid list_link list_token)  sh v p,
   sh <> Share.bot ->
   list_cell ls sh v p |-- valid_pointer p.
Proof.
 intros.
 unfold list_cell.
Abort.  (* probably not true; would be true with a direct (non-magic-wand)
      definition of list_cell *)

End LIST2.

Hint Rewrite @lseg_nil_eq : norm.

Hint Rewrite @lseg_eq using reflexivity: norm.

#[export] Hint Resolve lseg_local_facts : saturate_local.

#[export] Hint Resolve denote_tc_test_eq_split : valid_pointer.

End Links.

Arguments elemtype {cs} {list_structid} {list_link} {list_token} ls / .

