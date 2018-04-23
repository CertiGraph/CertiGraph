Require Import VST.floyd.proofauto.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.graph_relation.
Require Import RamifyCoq.graph.reachable_computable.
Require Import RamifyCoq.msl_application.Graph.
Require Import RamifyCoq.floyd_ext.share.
Require Import RamifyCoq.graph.FiniteGraph.
Require Import RamifyCoq.CertiGC.gc_mathgraph.
Require Import RamifyCoq.CertiGC.env_gc. 

Local Open Scope logic.

Local Coercion pg_lg : LabeledGraph >-> PreGraph.
Local Coercion lg_gg : GeneralGraph >-> LabeledGraph.

Definition V := val.

Parameter DV : Type.
Parameter DE : Type.
Parameter DG : Type.

Definition max_spaces : nat := 10.

Definition reachable_through_vertices_at (S: list addr) (g: env_Graph): mpred :=
  @vertices_at addr E _ _
               SGBA_GCgraph
               mpred
               (@SGP_VST fullshare g) 
               (@SGA_VST fullshare g) 
               (@reachable_through_set addr E _ _ g S)
              (@Graph_PointwiseGraph addr E _ _ (@SGBA_GCgraph addr _) LV LE LG (SGC_GCgraph) (lg_gg g)).

Definition gc_graph_pred (roots : list addr) (g : env_Graph) :=
  reachable_through_vertices_at roots g.

Local Open Scope nat_scope.

Fixpoint get_roots_helper n indices args : list addr :=
  match n with
  | 0 => []
  | _ => match indices with
        | [] => [] (* bad news *)
        | h :: t => (List.nth h args NullPointer) :: get_roots_helper (n-1) t args
        end
  end.

(* 
This is oversimplified. 
I actually need to take ti, a Tstruct of type _thread_info, and learn how to get the args array myself. 
*)
Definition get_roots (fi : list nat) (args : list addr) : list addr :=
  match fi with
  | _ :: n :: t => get_roots_helper n t args
  | _ => [] (* bad news *)
  end.

(* 
Questions:
1. can I just take a space, and then get the parameters from inside the space and then hook up those parameters to the function arguments when linking in PRE?
*)
Definition forward_spec :=
 DECLARE _forward
  WITH 	sh: wshare, 
  	g: env_Graph, 
  	start: pointer_val, 
  	limit: pointer_val, 
  	next: pointer_val, 
  	p: pointer_val,
        depth : nat,
        gen : nat, (* implicit, thanks to the caller *)
        roots_locs: list pointer_val 
                               
  PRE [ _from_start OF tptr (Tlong Unsigned noattr),
  	_from_limit OF tptr (Tlong Unsigned noattr),
  	_next OF tptr (tptr (Tlong Unsigned noattr)),
  	_p OF tptr (Tlong Unsigned noattr) ]
  EX roots,
    PROP (cleared_for_forward g gen start next limit p) (* Props of Coq type Prop, describing things that are forever true *)
    LOCAL ( temp _from_start (pointer_val_val start); 
  	    temp _from_limit (pointer_val_val limit);
  	    temp _next (pointer_val_val next);(* *)
  	    temp _p (pointer_val_val p) )
  	SEP (tarray roots_locs roots * graph_pred g roots) 
  POST [Tvoid]
  EX g' : Graph,
  EX roots,

          EX v: pointer_val, EX v': pointer_val, (* also, gen : nat *)
        PROP ()
(*((~(vvalid g \/) -> g = g' ) /\ (* etc *)
  	       ~ in_from g gen v \/ (* slightly off (re: quantifiers) *)
  	       (* "already copied" - adding a case to stepish *)
  	       (* update: seems there is no need; copyitem may cover it. *)
  	      copyitem g g' gen v v')*)
               (* strengthen stepish? *)
  	LOCAL ()
  	SEP (graph_pred g' roots).




Definition forward_roots_spec :=
 DECLARE _forward_roots
  WITH  sh: wshare,
        g: raw_GCgraph,
        start: pointer_val,
        limit: pointer_val,   
        next: pointer_val, 
        fi: pointer_val (* ?? *),
        ti: pointer_val (* ?? *)
  PRE [ _from_start OF tptr (Tlong Unsigned noattr),
        _from_limit OF tptr (Tlong Unsigned noattr),
        _next OF tptr (tptr (Tlong Unsigned noattr)),
        _fi OF tptr (Tlong Unsigned noattr),
        _ti OF tptr (Tstruct _thread_info noattr)]
    PROP () (* props of Coq type Prop, describing things that are forever true *) 
    LOCAL ( temp _from_start (pointer_val_val start); 
            temp _from_limit (pointer_val_val limit);
            temp _next (pointer_val_val next);
            temp _ti (pointer_val_val ti);
            temp _fi (pointer_val_val fi) )
    SEP (GC_graph g)
  POST [Tvoid]
    EX g' : raw_GCgraph, (* gen : nat *)
    PROP ()
          (* need the double indirection here
               want to say forward with a forall over the args array
            *)
    LOCAL ()
    SEP (GC_graph g /\ GC_graph g').

(*
void garbage_collect(fun_info fi, struct thread_info *ti)
 *)

(* need to fix fi's type. pointer_val is for c pointers *)
(* worth noting that fi is a unintnat* pointer *)
(* there are drastically different PRE and POST conditions depending on whether the heap was already created. how to encode? *)
(* whole_graph_valid seems like something I can borrow from Shengyi. *)
Definition garbage_collect_spec :=
  DECLARE _garbage_collect 
  WITH sh: wshare, g: env_Graph, fi : pointer_val (*???*), ti : pointer_val
  PRE [_fi OF (tptr tuint ), _ti OF (tptr (Tstruct _thread_info noattr))]
     PROP (whole_graph_valid g fi ti)
     LOCAL (temp _fi (pointer_val_val (*???*) fi); temp _ti (pointer_val_val ti))
     SEP (whole_graph sh g)
  POST [ tptr tvoid ]
  PROP (whole_graph_valid g' fi ti /\
        iso_from_roots g g' fi ti /\
        points_to_unalloc (*next ptr*))
     LOCAL ()
     SEP (whole_graph sh g').

(*
Definition whole_graph sh g x := (@full_graph_at mpred SAGA_VST pointer_val (SAG_VST sh) g x).
 *)


(* POSSIBLE HINT: do_generation basically calls forward_roots, then do_scan, and then aborts. the specs should be intimately related. *)
(* nextIsStart just says ``from->next=from->start'' *)
(* there are two complex postconditions that are basically specs of their own *)
Definition do_generation_spec :=
  DECLARE _do_generation 
  WITH sh: wshare, from : val, to : val, fi : ???, ti : val
     PRE [ temp _from OF (tptr (Tstruct _space noattr)),
           temp _to OF (tptr (Tstruct _space noattr)),
           temp _fi OF (tptr tuint),
           temp _ti OF (tptr (Tstruct _thread_info noattr))]
     PROP (some_form_of_validity g fi ti /\
           from_is_full g fi ti /\
           to_has_room g fi ti)
     LOCAL (temp _from from; temp _to to; temp _fi fi; temp _ti ti)
     SEP (whole_graph sh g)
  POST [ tptr tvoid ]
     EX g' : Graph, args' : ???, (* this will probably be a `` ti' '' instead. *)
                                 (* the new args will live inside the new ti *)    
     PROP (whole_graph sh g /\
          nextIsStart from /\
          ??? /\ ???)
     (* instead of writing this out, I want to reuse the specs for forward_roots and do_scan. Shengyi doesn't know how, but he did give me the hint above. Hmm. *)
     LOCAL ()
     SEP (whole_graph g /\ whole_graph g').

(* 
void do_scan(value *from_start,  /* beginning of from-space */
	     value *from_limit,  /* end of from-space */
	     value *scan,        /* start of unforwarded part of to-space */
 	     value **next)       /* next available spot in to-space */
*)
Definition do_scan_spec :=
  DECLARE _do_scan 
  WITH sh: wshare, start : val, limit : val, scan : val, next : val
     PRE [ _from_start OF (tptr tint),
           _from_limit OF (tptr tint),
           _scan OF (tptr tint),
           _next OF (tptr (tptr tint))]
     PROP (no_pointers_from (*to_start*) (*to_scan*) (*from_start*) (*from_limit*))
     LOCAL (temp _from_start start; temp _from_limit limit;
            temp _scan scan; temp _next next)  
     SEP ()
  POST [ tptr tvoid ]
  PROP (subgraphs_iso g g' fi ti /\
        (* want to say that only to and from were even touched *) /\
        (* to->scan' == to->next'
	to->scan' ≥ to->scan 
	to->next' ≥ to->next *) /\
        no_pointers_from (*to_start*) (*to_next'*) (*from_start*) (*from_limit*))
     LOCAL ()
     SEP ().

Definition forward_roots_spec :=
  DECLARE _forward_roots 
  WITH sh: wshare, start : val, limit : val, ti : val, fi : ??, next : val
     PRE [ _from_start OF (tptr tint),
           _from_limit OF (tptr tint),
           _next OF (tptr (tptr tint)),
           _fi OF (tptr tuint),
           _ti OF (tptr (Tstruct _thread_info noattr))]
     PROP ()
     LOCAL (temp _from_start start; temp _from_limit limit;
            temp _next next; temp _fi fi; temp _ti ti)
     SEP ()
  POST [ tptr tvoid ]
  PROP (subgraphs_iso g g' fi ti /\
       (* to->next' ≥ to->next *) /\ 
        no_pointers_from  (*live roots slots of the args array *) (*from_start*) (*from_limit*))
     LOCAL ()
     SEP ().



(***********************)
(** below is UF stuff **)
(***********************)

Definition mallocN_spec :=
 DECLARE _mallocN
  WITH sh: wshare, n:Z
  PRE [ 67%positive OF tint]
     PROP (0 <= n <= Int.max_signed)
     LOCAL (temp 67%positive (Vint (Int.repr n)))
     SEP ()
  POST [ tptr tvoid ]
     EX v: addr,
     PROP ()
     LOCAL (temp ret_temp (pointer_val_val v))
     SEP (data_at sh node_type (pointer_val_val null, (Vint (Int.repr 0)))
              (pointer_val_val v)).

Definition find_spec :=
 DECLARE _find
  WITH sh: wshare, g: Graph, x: pointer_val
  PRE [ _x OF (tptr (Tstruct _Node noattr))]
          PROP  (vvalid g x)
          LOCAL (temp _x (pointer_val_val x))
          SEP   (whole_graph sh g)
  POST [ tptr (Tstruct _Node noattr) ]
        EX g': Graph, EX rt : pointer_val,
        PROP (uf_equiv g g' /\ uf_root g' x rt)
        LOCAL (temp ret_temp (pointer_val_val rt))
        SEP (whole_graph sh g').

Definition unionS_spec :=
 DECLARE _unionS
  WITH sh: wshare, g: Graph, x: pointer_val, y: pointer_val
  PRE [ _x OF (tptr (Tstruct _Node noattr)), _y OF (tptr (Tstruct _Node noattr))]
          PROP  (vvalid g x /\ vvalid g y)
          LOCAL (temp _x (pointer_val_val x); temp _y (pointer_val_val y))
          SEP   (whole_graph sh g)
  POST [ Tvoid ]
        EX g': Graph,
        PROP (uf_union g x y g')
        LOCAL()
        SEP (whole_graph sh g').

Definition makeSet_spec :=
  DECLARE _makeSet
  WITH sh: wshare, g: Graph
    PRE []
      PROP ()
      LOCAL ()
      SEP (whole_graph sh g)
    POST [tptr (Tstruct _Node noattr)]
      EX g': Graph, EX rt: pointer_val,
      PROP (~ vvalid g rt /\ vvalid g' rt /\ is_partial_graph g g')
      LOCAL (temp ret_temp (pointer_val_val rt))
      SEP (whole_graph sh g').

Definition Vprog : varspecs := nil.

Definition Gprog : funspecs := mallocN_spec :: makeSet_spec :: find_spec :: unionS_spec ::nil.

Lemma body_makeSet: semax_body Vprog Gprog f_makeSet makeSet_spec.
Proof.
  start_function.
  forward_call (sh, 8).
  - compute. split; intros; inversion H.
  - Intros x.
    assert_PROP (x <> null) as x_not_null by (entailer !; destruct H0 as [? _]; apply H0).
    assert_PROP (~ vvalid g x) by (entailer; apply (@vertices_at_sepcon_unique_1x _ _ _ _ SGBA_VST _ _ (SGA_VST sh) (SGAvs_VST sh) g x (vvalid g) (O, null))).
    forward. forward. forward.
    change (@field_at CompSpecs sh node_type [] (Vint (Int.repr 0), pointer_val_val x)) with (@data_at CompSpecs sh node_type (Vint (Int.repr 0), pointer_val_val x)).
    apply (exp_right (make_set_Graph O tt tt x g x_not_null H)). entailer. apply (exp_right x). entailer !.
    + split; simpl; [right | apply is_partial_make_set_pregraph]; auto.
    + assert (Coqlib.Prop_join (vvalid g) (eq x) (vvalid (make_set_Graph 0%nat tt tt x g x_not_null H))). {
        simpl; hnf; split; intros; [unfold graph_gen.addValidFunc | subst a]; intuition.
      } assert (vgamma (make_set_Graph O tt tt x g x_not_null H) x = (O, x)). {
        simpl. f_equal.
        - destruct (SGBA_VE x x); [| hnf in c; unfold Equivalence.equiv in c; exfalso]; auto.
        - unfold graph_gen.updateEdgeFunc. destruct (EquivDec.equiv_dec (x, tt) (x, tt)). 2: compute in c; exfalso; auto. destruct (SGBA_VE null null); auto.
          hnf in c. unfold Equivalence.equiv in c. exfalso; auto.
      } rewrite <- (vertices_at_sepcon_1x (make_set_Graph 0%nat tt tt x g x_not_null H) x (vvalid g) _ (O, x)); auto. apply sepcon_derives. 1: entailer !.
      assert (vertices_at sh (vvalid g) g = vertices_at sh (vvalid g) (make_set_Graph O tt tt x g x_not_null H)). {
        apply vertices_at_vertices_identical. simpl. hnf. intros. destruct a as [y ?]. unfold Morphisms_ext.app_sig. simpl. unfold graph_gen.updateEdgeFunc. f_equal.
        - destruct (SGBA_VE y x); [hnf in e; subst y; exfalso |]; auto.
        - destruct (EquivDec.equiv_dec (x, tt) (y, tt)); auto. hnf in e. inversion e. subst y. exfalso; auto.
      } rewrite <- H5. entailer.
Qed.

Lemma false_Cne_eq: forall x y, typed_false tint (force_val (sem_cmp_pp Cne (pointer_val_val x) (pointer_val_val y))) -> x = y.
Proof.
  intros. hnf in H. destruct x, y; inversion H; auto. simpl in H. clear H1. unfold sem_cmp_pp in H. simpl in H. destruct (eq_block b b0).
  - destruct (Int.eq i i0) eqn:? .
    + symmetry in Heqb1. apply binop_lemmas2.int_eq_true in Heqb1. subst; auto.
    + simpl in H. inversion H.
  - simpl in H. inversion H.
Qed.

Lemma true_Cne_neq: forall x y, typed_true tint (force_val (sem_cmp_pp Cne (pointer_val_val x) (pointer_val_val y))) -> x <> y.
Proof.
  intros. hnf in H. destruct x, y; inversion H; [|intro; inversion H0..]. simpl in H. clear H1. unfold sem_cmp_pp in H. simpl in H. destruct (eq_block b b0).
  - destruct (Int.eq i i0) eqn:? .
    + simpl in H. inversion H.
    + subst b0. apply int_eq_false_e in Heqb1. intro. inversion H0. auto.
  - intro. inversion H0. auto.
Qed.

Lemma ADMIT: forall P: Prop, P.
Admitted.

Lemma body_find: semax_body Vprog Gprog f_find find_spec.
Proof.
  start_function.
  remember (vgamma g x) as rpa eqn:?H. destruct rpa as [r pa].
  (* p = x -> parent; *)
  localize
    (PROP  ()
     LOCAL (temp _x (pointer_val_val x))
     SEP  (data_at sh node_type (vgamma2cdata (vgamma g x)) (pointer_val_val x))).
  rewrite <- H0. simpl vgamma2cdata.
  eapply semax_ram_seq;
    [ subst RamFrame RamFrame0; unfold abbreviate;
      repeat apply eexists_add_stats_cons; constructor
    | load_tac
    | abbreviate_semax_ram].
  unlocalize
    (PROP  ()
     LOCAL (temp _p (pointer_val_val pa); temp _x (pointer_val_val x))
     SEP  (whole_graph sh g)).
  Grab Existential Variables.
  Focus 2. {
    simplify_ramif. rewrite <- H0. simpl.
    apply (@vertices_at_ramif_1_stable _ _ _ _ SGBA_VST _ _ (SGA_VST sh) g (vvalid g) x (r, pa)); auto.
  } Unfocus.
  unfold semax_ram.
  (* if (p != x) { *)
  forward_if_tac
    (EX g': Graph, EX rt : pointer_val,
     PROP (uf_equiv g g' /\ uf_root g' x rt)
     LOCAL (temp _p (pointer_val_val rt); temp _x (pointer_val_val x))
     SEP (whole_graph sh g'));
    [apply ADMIT | | gather_current_goal_with_evar ..].
  (* p0 = find(p); *)
  forward_call (sh, g, pa). 1: symmetry in H0; apply valid_parent in H0; auto.
  Intros vret. destruct vret as [g' root]. simpl fst in *. simpl snd in *. forward. symmetry in H0.
  pose proof (true_Cne_neq _ _ H1).
  assert (weak_valid g' root) by (right; destruct H3; apply reachable_foot_valid in H3; auto).
  assert (vvalid g' x) by (destruct H2 as [? _]; rewrite <- H2; apply H).
  assert (~ reachable g' root x) by (apply (uf_equiv_not_reachable g g' x r pa root); auto).
  assert (vertices_at sh (vvalid (Graph_gen_redirect_parent g' x root H5 H6 H7)) (Graph_gen_redirect_parent g' x root H5 H6 H7) =
          vertices_at sh (vvalid g') (Graph_gen_redirect_parent g' x root H5 H6 H7)). {
    apply vertices_at_Same_set. unfold Ensembles.Same_set, Ensembles.Included, Ensembles.In. simpl. intuition. }
  remember (vgamma g' x) as rpa eqn:?H. destruct rpa as [r' pa']. symmetry in H9.
  localize
   (PROP  ()
    LOCAL (temp _p (pointer_val_val root); temp _x (pointer_val_val x))
    SEP   (data_at sh node_type (Vint (Int.repr (Z.of_nat r')), pointer_val_val pa')
                   (pointer_val_val x))).
    eapply semax_ram_seq';
    [ subst RamFrame RamFrame0; unfold abbreviate;
      repeat apply eexists_add_stats_cons; constructor
    | store_tac
    | abbreviate_semax_ram].
    assert (force_val (sem_cast_neutral (pointer_val_val root)) = pointer_val_val root) by (destruct root; simpl; auto). rewrite H10. clear H10.
    change (@field_at CompSpecs sh node_type [] (Vint (Int.repr (Z.of_nat r')), pointer_val_val root) (pointer_val_val x)) with
        (@data_at CompSpecs sh node_type (Vint (Int.repr (Z.of_nat r')), pointer_val_val root) (pointer_val_val x)).
  unlocalize
   (PROP ()
    LOCAL (temp _p (pointer_val_val root); temp _x (pointer_val_val x))
    SEP (whole_graph sh (Graph_gen_redirect_parent g' x root H5 H6 H7))).
  Grab Existential Variables.
  Focus 3. { Intros g' rt. forward. apply (exp_right g'). entailer !. apply (exp_right rt). entailer !. } Unfocus.
  Focus 3. {
    forward. apply (exp_right g). apply (exp_right x). entailer ! . apply false_Cne_eq in H1. subst pa. split; [|split]; auto.
    - apply (uf_equiv_refl _  (liGraph g)).
    - apply uf_root_vgamma with (n := r); auto.
  } Unfocus.
  Focus 2. {
    simplify_ramif. rewrite H8. apply (@graph_gen_redirect_parent_ramify _ (sSGG_VST sh)); auto. destruct H3.
    apply reachable_foot_valid in H3. intro. subst root. apply (valid_not_null g' null H3). simpl. auto.
  } Unfocus.
  rewrite H8. unfold semax_ram. forward. apply (exp_right (Graph_gen_redirect_parent g' x root H5 H6 H7)). apply (exp_right root). rewrite H8. entailer !. split.
  - apply (graph_gen_redirect_parent_equiv g g' x r pa); auto.
  - simpl. apply (uf_root_gen_dst_same g' (liGraph g') x x root); auto.
    + rewrite <- (uf_equiv_root_the_same g); auto. apply (uf_root_edge _ (liGraph g) _ pa); [| apply vgamma_not_dst with r | rewrite (uf_equiv_root_the_same g g')]; auto.
    + apply reachable_refl; auto.
Qed.

(* Print Assumptions body_find. *)

Lemma true_Ceq_eq: forall x y, typed_true tint (force_val (sem_cmp_pp Ceq (pointer_val_val x) (pointer_val_val y))) -> x = y.
Proof.
  intros. hnf in H. destruct x, y; inversion H; auto. simpl in H. clear H1. unfold sem_cmp_pp in H. simpl in H. destruct (eq_block b b0).
  - destruct (Int.eq i i0) eqn:? .
    + symmetry in Heqb1. apply binop_lemmas2.int_eq_true in Heqb1. subst; auto.
    + simpl in H. inversion H.
  - simpl in H. inversion H.
Qed.

Lemma false_Ceq_neq: forall x y, typed_false tint (force_val (sem_cmp_pp Ceq (pointer_val_val x) (pointer_val_val y))) -> x <> y.
Proof.
  intros. hnf in H. destruct x, y; inversion H; [|intro; inversion H0..]. simpl in H. clear H1. unfold sem_cmp_pp in H. simpl in H. destruct (eq_block b b0).
  - destruct (Int.eq i i0) eqn:? .
    + simpl in H. inversion H.
    + subst b0. apply int_eq_false_e in Heqb1. intro. inversion H0. auto.
  - intro. inversion H0. auto.
Qed.

Lemma body_unionS: semax_body Vprog Gprog f_unionS unionS_spec.
Proof.
  start_function.
  destruct H.
  forward_call (sh, g, x). Intros vret. destruct vret as [g1 x_root]. simpl fst in *. simpl snd in *.
  assert (vvalid g1 y) by (destruct H1 as [? _]; rewrite <- H1; apply H0).
  forward_call (sh, g1, y). Intros vret. destruct vret as [g2 y_root]. simpl fst in *. simpl snd in *.
  forward_if_tac
    (PROP (x_root <> y_root)
     LOCAL (temp _yRoot (pointer_val_val y_root); temp _xRoot (pointer_val_val x_root);
     temp _x (pointer_val_val x); temp _y (pointer_val_val y))
     SEP (vertices_at sh (vvalid g2) g2)). 1: apply ADMIT.
  Focus 1. { forward. apply (exp_right g2). entailer !; auto. apply true_Ceq_eq in H6. subst y_root. apply (the_same_root_union g g1 g2 x y x_root); auto. } Unfocus.
  Focus 1. { forward. apply false_Ceq_neq in H6. entailer. } Unfocus.

  (* xRank = xRoot -> rank; *)
  Intros. remember (vgamma g2 x_root) as rpa eqn:?H. destruct rpa as [rankXRoot paXRoot]. symmetry in H7.
  localize
    (PROP  ()
     LOCAL (temp _xRoot (pointer_val_val x_root))
     SEP  (data_at sh node_type (vgamma2cdata (vgamma g2 x_root)) (pointer_val_val x_root))).
  rewrite H7. simpl vgamma2cdata. apply -> ram_seq_assoc.
  eapply semax_ram_seq;
  [subst RamFrame RamFrame0; unfold abbreviate;
   repeat apply eexists_add_stats_cons; constructor
  | load_tac
  | abbreviate_semax_ram].
  unlocalize
    (PROP  ()
     LOCAL (temp _xRank (Vint (Int.repr (Z.of_nat rankXRoot))); temp _xRoot (pointer_val_val x_root); temp _yRoot (pointer_val_val y_root);
            temp _x (pointer_val_val x); temp _y (pointer_val_val y))
     SEP  (whole_graph sh g2)).
  Grab Existential Variables.
  Focus 2. {
    simplify_ramif. rewrite H7. simpl. apply (@vertices_at_ramif_1_stable _ _ _ _ SGBA_VST _ _ (SGA_VST sh) g2 (vvalid g2) x_root (rankXRoot, paXRoot)); auto.
    destruct H4 as [? _]. rewrite <- H4. destruct H2. apply reachable_foot_valid in H2. apply H2.
  } Unfocus.

  (* yRank = yRoot -> rank; *)
  remember (vgamma g2 y_root) as rpa eqn:?H. destruct rpa as [rankYRoot paYRoot]. symmetry in H8.
  localize
    (PROP  ()
     LOCAL (temp _yRoot (pointer_val_val y_root))
     SEP  (data_at sh node_type (vgamma2cdata (vgamma g2 y_root)) (pointer_val_val y_root))).
  rewrite H8. simpl vgamma2cdata. apply -> ram_seq_assoc.
  eapply semax_ram_seq;
  [subst RamFrame RamFrame0; unfold abbreviate;
   repeat apply eexists_add_stats_cons; constructor
  | load_tac
  | abbreviate_semax_ram].
  unlocalize
    (PROP  ()
     LOCAL (temp _xRank (Vint (Int.repr (Z.of_nat rankXRoot))); temp _yRank (Vint (Int.repr (Z.of_nat rankYRoot))); temp _xRoot (pointer_val_val x_root);
            temp _yRoot (pointer_val_val y_root); temp _x (pointer_val_val x); temp _y (pointer_val_val y))
     SEP  (whole_graph sh g2)).
  Grab Existential Variables.
  Focus 2. {
    simplify_ramif. rewrite H8. simpl. apply (@vertices_at_ramif_1_stable _ _ _ _ SGBA_VST _ _ (SGA_VST sh) g2 (vvalid g2) y_root (rankYRoot, paYRoot)); auto.
    destruct H5. apply reachable_foot_valid in H5. apply H5.
  } Unfocus.

  unfold semax_ram.
  forward_if_tac
    (EX g': Graph,
     PROP (uf_union g x y g')
          LOCAL (temp _xRank (Vint (Int.repr (Z.of_nat rankXRoot))); temp _yRank (Vint (Int.repr (Z.of_nat rankYRoot)));
                 temp _xRoot (pointer_val_val x_root); temp _yRoot (pointer_val_val y_root);
                 temp _x (pointer_val_val x); temp _y (pointer_val_val y))
     SEP (whole_graph sh g')).
  Focus 3. { Intros g'. forward. apply (exp_right g'). entailer. } Unfocus.
  Focus 2. { gather_current_goal_with_evar. } Unfocus.
  assert (weak_valid g2 y_root) by (right; destruct H5; apply reachable_foot_valid in H5; apply H5).
  assert (vvalid g2 x_root) by (destruct H4 as [? _]; rewrite <- H4; destruct H2; apply reachable_foot_valid in H2; apply H2).
  assert (~ reachable g2 y_root x_root) by (intro; destruct H5; specialize (H13 _ H12); auto).
  assert (vertices_at sh (vvalid (Graph_gen_redirect_parent g2 x_root y_root H10 H11 H12)) (Graph_gen_redirect_parent g2 x_root y_root H10 H11 H12) =
          vertices_at sh (vvalid g2) (Graph_gen_redirect_parent g2 x_root y_root H10 H11 H12)). {
    apply vertices_at_Same_set. unfold Ensembles.Same_set, Ensembles.Included, Ensembles.In. simpl. intuition. }

  (* xRoot -> parent = yRoot; *)
  localize
   (PROP  ()
    LOCAL (temp _xRoot (pointer_val_val x_root); temp _yRoot (pointer_val_val y_root))
    SEP   (data_at sh node_type (vgamma2cdata (vgamma g2 x_root)) (pointer_val_val x_root))).
  rewrite H7. simpl vgamma2cdata.
  eapply semax_ram_seq';
    [ subst RamFrame RamFrame0; unfold abbreviate;
      repeat apply eexists_add_stats_cons; constructor
    | store_tac
    | abbreviate_semax_ram].
  assert (force_val (sem_cast_neutral (pointer_val_val y_root)) = pointer_val_val y_root) by (destruct y_root; simpl; auto). rewrite H14. clear H14.
  change (@field_at CompSpecs sh node_type [] (Vint (Int.repr (Z.of_nat rankXRoot)), pointer_val_val y_root) (pointer_val_val x_root)) with
      (@data_at CompSpecs sh node_type (Vint (Int.repr (Z.of_nat rankXRoot)), pointer_val_val y_root) (pointer_val_val x_root)).
  unlocalize
   (PROP ()
         LOCAL (temp _xRank (Vint (Int.repr (Z.of_nat rankXRoot))); temp _yRank (Vint (Int.repr (Z.of_nat rankYRoot)));
                temp _xRoot (pointer_val_val x_root); temp _yRoot (pointer_val_val y_root);
                temp _x (pointer_val_val x); temp _y (pointer_val_val y))
    SEP (whole_graph sh (Graph_gen_redirect_parent g2 x_root y_root H10 H11 H12))).
  Grab Existential Variables.
  Focus 2. {
    simplify_ramif. rewrite H7. simpl vgamma2cdata. rewrite H13. apply (@graph_gen_redirect_parent_ramify _ (sSGG_VST sh)); auto. destruct H5.
    apply reachable_foot_valid in H5. intro. subst y_root. apply (valid_not_null g2 null H5). simpl. auto.
  } Unfocus.
  Focus 1. {
    unfold semax_ram. forward. apply (exp_right (Graph_gen_redirect_parent g2 x_root y_root H10 H11 H12)). entailer !.
    apply (diff_root_union_1 g g1 g2 x y x_root y_root); auto.
  } Unfocus.

  assert (weak_valid g2 x_root) by (right; destruct H4 as [? _]; rewrite <- H4; destruct H2; apply reachable_foot_valid in H2; apply H2).
  assert (vvalid g2 y_root) by (destruct H5; apply reachable_foot_valid in H5; apply H5).
  assert (~ reachable g2 x_root y_root) by (intro; rewrite (uf_equiv_root_the_same g1 g2) in H2; auto; destruct H2; specialize (H13 _ H12); auto).
  assert (vertices_at sh (vvalid (Graph_gen_redirect_parent g2 y_root x_root H10 H11 H12)) (Graph_gen_redirect_parent g2 y_root x_root H10 H11 H12) =
          vertices_at sh (vvalid g2) (Graph_gen_redirect_parent g2 y_root x_root H10 H11 H12)). {
    apply vertices_at_Same_set. unfold Ensembles.Same_set, Ensembles.Included, Ensembles.In. simpl. intuition. }
  forward_if_tac
    (EX g': Graph,
     PROP (uf_union g x y g')
          LOCAL (temp _xRank (Vint (Int.repr (Z.of_nat rankXRoot))); temp _yRank (Vint (Int.repr (Z.of_nat rankYRoot)));
                 temp _xRoot (pointer_val_val x_root); temp _yRoot (pointer_val_val y_root);
                 temp _x (pointer_val_val x); temp _y (pointer_val_val y))
     SEP (whole_graph sh g')).
  Focus 3. { unfold POSTCONDITION. unfold abbreviate. rewrite overridePost_overridePost. intros. apply andp_left2. auto. } Unfocus.
  Focus 2. { gather_current_goal_with_evar. } Unfocus.

  (* yRoot -> parent = xRoot; *)
  localize
   (PROP  ()
    LOCAL (temp _xRoot (pointer_val_val x_root); temp _yRoot (pointer_val_val y_root))
    SEP   (data_at sh node_type (vgamma2cdata (vgamma g2 y_root)) (pointer_val_val y_root))).
  rewrite H8. simpl vgamma2cdata.
  eapply semax_ram_seq';
    [ subst RamFrame RamFrame0; unfold abbreviate;
      repeat apply eexists_add_stats_cons; constructor
    | store_tac
    | abbreviate_semax_ram].
  assert (force_val (sem_cast_neutral (pointer_val_val x_root)) = pointer_val_val x_root) by (destruct x_root; simpl; auto). rewrite H15. clear H15.
  change (@field_at CompSpecs sh node_type [] (Vint (Int.repr (Z.of_nat rankYRoot)), pointer_val_val x_root) (pointer_val_val y_root)) with
      (@data_at CompSpecs sh node_type (Vint (Int.repr (Z.of_nat rankYRoot)), pointer_val_val x_root) (pointer_val_val y_root)).
  unlocalize
   (PROP ()
         LOCAL (temp _xRank (Vint (Int.repr (Z.of_nat rankXRoot))); temp _yRank (Vint (Int.repr (Z.of_nat rankYRoot)));
                temp _xRoot (pointer_val_val x_root); temp _yRoot (pointer_val_val y_root);
                temp _x (pointer_val_val x); temp _y (pointer_val_val y))
    SEP (whole_graph sh (Graph_gen_redirect_parent g2 y_root x_root H10 H11 H12))).
  Grab Existential Variables.
  Focus 2. {
    simplify_ramif. rewrite H8. simpl vgamma2cdata. rewrite H13. apply (@graph_gen_redirect_parent_ramify _ (sSGG_VST sh)); auto. destruct H2.
    apply reachable_foot_valid in H2. intro. subst x_root. apply (valid_not_null g1 null H2). simpl. auto.
  } Unfocus.
  Focus 1. {
    unfold semax_ram. forward. apply (exp_right (Graph_gen_redirect_parent g2 y_root x_root H10 H11 H12)). entailer !.
    apply (diff_root_union_2 g g1 g2 x y x_root y_root); auto.
  } Unfocus.

  (* yRoot -> parent = xRoot; *)
  localize
   (PROP  ()
    LOCAL (temp _xRoot (pointer_val_val x_root); temp _yRoot (pointer_val_val y_root))
    SEP   (data_at sh node_type (vgamma2cdata (vgamma g2 y_root)) (pointer_val_val y_root))).
  rewrite H8. simpl vgamma2cdata.
  eapply semax_ram_seq;
    [ subst RamFrame RamFrame0; unfold abbreviate;
      repeat apply eexists_add_stats_cons; constructor
    | store_tac
    | abbreviate_semax_ram].
  assert (force_val (sem_cast_neutral (pointer_val_val x_root)) = pointer_val_val x_root) by (destruct x_root; simpl; auto). rewrite H15. clear H15.
  change (@field_at CompSpecs sh node_type [] (Vint (Int.repr (Z.of_nat rankYRoot)), pointer_val_val x_root) (pointer_val_val y_root)) with
      (@data_at CompSpecs sh node_type (Vint (Int.repr (Z.of_nat rankYRoot)), pointer_val_val x_root) (pointer_val_val y_root)).
  unlocalize
   (PROP ()
         LOCAL (temp _xRank (Vint (Int.repr (Z.of_nat rankXRoot))); temp _yRank (Vint (Int.repr (Z.of_nat rankYRoot)));
                temp _xRoot (pointer_val_val x_root); temp _yRoot (pointer_val_val y_root);
                temp _x (pointer_val_val x); temp _y (pointer_val_val y))
    SEP (whole_graph sh (Graph_gen_redirect_parent g2 y_root x_root H10 H11 H12))).
  Grab Existential Variables.
  Focus 2. {
    simplify_ramif. rewrite H8. simpl vgamma2cdata. rewrite H13. apply (@graph_gen_redirect_parent_ramify _ (sSGG_VST sh)); auto. destruct H2.
    apply reachable_foot_valid in H2. intro. subst x_root. apply (valid_not_null g1 null H2). simpl. auto.
  } Unfocus. clear H13.
  remember (Graph_gen_redirect_parent g2 y_root x_root H10 H11 H12) as g3.
  assert (uf_union g x y g3) by (rewrite Heqg3; simpl; apply (diff_root_union_2 g g1 g2 x y x_root y_root); auto).

  (* xRoot -> rank = xRank + 1; *)
  localize
   (PROP  ()
    LOCAL (temp _xRoot (pointer_val_val x_root); temp _xRank (Vint (Int.repr (Z.of_nat rankXRoot))))
    SEP   (data_at sh node_type (vgamma2cdata (vgamma g2 x_root)) (pointer_val_val x_root))).
  rewrite H7. simpl vgamma2cdata.
  eapply semax_ram_seq';
    [ subst RamFrame RamFrame0; unfold abbreviate;
      repeat apply eexists_add_stats_cons; constructor
    | store_tac
    | abbreviate_semax_ram].
  rewrite add_repr. replace (Z.of_nat rankXRoot + 1) with (Z.of_nat (rankXRoot + 1)). 2: rewrite Nat2Z.inj_add; simpl; auto.
  change (@field_at CompSpecs sh node_type [] (Vint (Int.repr (Z.of_nat (rankXRoot + 1))), pointer_val_val paXRoot) (pointer_val_val x_root)) with
      (@data_at CompSpecs sh node_type (Vint (Int.repr (Z.of_nat (rankXRoot + 1))), pointer_val_val paXRoot) (pointer_val_val x_root)).
  unlocalize
   (PROP ()
    LOCAL (temp _xRank (Vint (Int.repr (Z.of_nat rankXRoot))); temp _yRank (Vint (Int.repr (Z.of_nat rankYRoot)));
           temp _xRoot (pointer_val_val x_root); temp _yRoot (pointer_val_val y_root);
           temp _x (pointer_val_val x); temp _y (pointer_val_val y))
    SEP (whole_graph sh (Graph_vgen g3 x_root (rankXRoot + 1)%nat))).
  Grab Existential Variables.
  Focus 2. {
    simplify_ramif.
    assert (vertices_at sh (vvalid (Graph_vgen g3 x_root (rankXRoot + 1)%nat)) (Graph_vgen g3 x_root (rankXRoot + 1)%nat) =
            vertices_at sh (vvalid g3) (Graph_vgen g3 x_root (rankXRoot + 1)%nat)). {
      apply vertices_at_Same_set. unfold Ensembles.Same_set, Ensembles.Included, Ensembles.In. simpl. intuition.
    } rewrite H15. clear H15. rewrite H7. simpl vgamma2cdata. apply (@graph_vgen_ramify _ (sSGG_VST sh)).
    - rewrite Heqg3. simpl. destruct H4 as [? _]; rewrite <- H4; destruct H2; apply reachable_foot_valid in H2; apply H2.
    - apply (graph_gen_redirect_parent_vgamma _ _ _ rankXRoot paXRoot) in Heqg3; auto.
  } Unfocus.
  unfold semax_ram. forward. apply (exp_right (Graph_vgen g3 x_root (rankXRoot + 1)%nat)). entailer !.
Qed. (* 205.811 secs *)
