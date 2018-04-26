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
Require Import RamifyCoq.CertiGC.orders.

Local Open Scope logic.

Local Coercion pg_lg : LabeledGraph >-> PreGraph.
Local Coercion lg_gg : GeneralGraph >-> LabeledGraph.

Context {V : Type}. (* These will be CompCert addresses. *)
Context {OLE : Ord V}. Existing Instance OLE.

(* This is currently very explicit, partly so I can understand each and every parameter. Let's leave it like this for a while. I'll make it more succinct later. *)
Definition reachable_through_vertices_at (S: list addr) (g: env_Graph): mpred :=
  @vertices_at addr E _ _
               SGBA_GCgraph
               mpred
               (@SGP_VST fullshare g) 
               (@SGA_VST fullshare g) 
               (@reachable_through_set addr E _ _ g S)
              (@Graph_PointwiseGraph addr E _ _ (@SGBA_GCgraph addr _) LV LE LG (SGC_GCgraph) (lg_gg g)).

Local Open Scope nat_scope. 

Fixpoint get_roots_helper n indices args : list addr :=
  match n with
  | 0 => [] (* done cleanly *)
  | _ => match indices with
        | [] => [] (* bad news - we wanted more items but the list was empty *)
        | h :: t => (List.nth h args NullPointer) :: get_roots_helper (n-1) t args
        end
  end.

(* 
This is oversimplified. 
I actually need to take ti, which is a Tstruct of type _thread_info, and learn how to extract the args array myself. Right now I'm simply assuming that the args array was given to me, and I just need to select the correct items from args array. This is done in a fairly obvious way using fun_info.   
*)
Definition get_roots (fun_info : list nat) (args : list addr) : list addr :=
  match fun_info with
  | _ :: n :: t => get_roots_helper n t args
  | _ => [] (* Bad news! We shouldn't reach here. *)
  end.

Local Close Scope nat_scope. 

(* Here, roots has to be a cleaned-up list of addresses that we have gotten (via double indirection) from thread_info. See the function get_roots above. *)
Definition gc_graph_pred (roots : list addr) (g : env_Graph) :=
  reachable_through_vertices_at roots g.


Local Open Scope ord. 

(* 
This is a little Prop which will go into the forward spec. Just a space for simple facts about start, next, limit, p, etc. Currently very silly.
 *)
Definition cleared_for_forward (g: env_Graph) (gen: nat) (sta nxt lim p : addr) :=
  match get_space g gen, get_space g (gen+1) with
  | None, _ => False
  | _, None => False
  | Some sp, Some sp' => 
    (sta = start sp) /\
    (lim = limit sp) /\
    (sta <= p <= lim) /\
    (start sp' <= nxt <= limit sp')
  end.

Local Close Scope ord. 


(* 
Known Issues/Comments:
1. can I just take a space, and then get the parameters from inside the space and then hook up those parameters to the function arguments when linking in PRE?
2. Need an array mpred in PRE SEP. It's something like "sepcon (array mpred) (graph mpred)". Probably worth defining outside in a function because we'll need to cook up many such mpreds.
3. If you see the WITH, you'll see that we have a "gen : nat" in there. The idea is that the caller (or the caller's caller) will know the generation number, (it will just be the i in the for loop) and so it should be possible for forward to know what the i is. If this is actually the case, we'll benefit greatly because we'll know the current generation number for free.
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
  EX roots : list addr,
    PROP (cleared_for_forward g gen start next limit p)
    LOCAL ( temp _from_start (pointer_val_val start); 
  	    temp _from_limit (pointer_val_val limit);
  	    temp _next (pointer_val_val next);(* *)
  	    temp _p (pointer_val_val p) )
  	SEP ((*tarray roots_locs roots *) gc_graph_pred roots g) 
  POST [Tvoid]
  EX g' : Graph, EX roots: list addr,
  EX v: pointer_val, EX v': pointer_val,
  PROP ()
       (* 
Here we probably want to appeal to stepish from gc_mathgraph. This whole thing is probably just a case of stepish called copyitem. Anyway, some ideas are below...  
       ((~(vvalid g \/)) -> g = g' ) /\ (* etc *)
        ~ in_from g gen v \/ (* check quantifiers? *) 
        copyitem g g' gen v v') (* strengthen stepish?*)  
*)
  	LOCAL ()
  	SEP (gc_graph_pred roots g').


(* *********************************************)
(* The stuff below is not currently maintained *)
(* *********************************************)

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