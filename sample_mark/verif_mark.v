Require Import VST.floyd.proofauto.
Require Import RamifyCoq.sample_mark.mark.

Local Open Scope logic.

Instance CompSpecs : compspecs := compspecs_program prog.
Instance CS_legal : compspecs_legal CompSpecs.
Proof. prove_CS_legal. Qed.

Variable BiMathGraph: Type.
Variable graph: val -> BiMathGraph -> mpred.
Variable mark_graph: BiMathGraph -> val -> BiMathGraph.

Definition mark_spec :=
 DECLARE _mark
  WITH g: BiMathGraph, x: val
  PRE [ _x OF (tptr (Tstruct _Node noattr))]
          PROP  ()
          LOCAL (temp _x x)
          SEP   (`(graph x g))
  POST [ tint ]
        PROP ()
        LOCAL()
        SEP (`(graph x (mark_graph g x))).

Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog u
  POST [ tint ] main_post prog u.

Definition Vprog : varspecs := (_hd, tptr (talignas 4%N (Tstruct _Node noattr)))::(_n, (talignas 4%N (Tstruct _Node noattr)))::nil.

Definition Gprog : funspecs := mark_spec :: main_spec::nil.
