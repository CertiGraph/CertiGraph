Require Import VST.floyd.base.
Require Import VST.floyd.field_at.

Lemma denote_tc_comparable_admit: forall {cs : compspecs} {csl: compspecs_legal cs} sh t v p, data_at sh t v p |-- denote_tc_comparable p (Vint (Int.repr 0)).
Admitted.

Hint Resolve denote_tc_comparable_admit: norm.
Hint Resolve denote_tc_comparable_admit: cancel.


