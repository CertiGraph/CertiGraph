# Andrew Appel PDF comments summary

Source PDF:
`/Users/shengyiwang/Downloads/draft-experience-report-appel-comments.pdf`.

This note summarizes the visible PDF annotations and highlighted text from the
commented draft.  The current PDF page tree contains 42 non-link, non-popup
annotations; some of them are paired deletion/insertion marks and are therefore
merged below into single revision items.  The extraction used PDF annotation
objects plus page renderings.  "Highlighted text" is the visible page text that
appears to be highlighted or otherwise marked.  A few insertion and text-note
comments do not select a complete phrase; those are recorded as insertion
locations or page notes.

## Overall revision themes

1. Write for a reader who knows verification and perhaps AI-assisted
   development, but does not know generational copying garbage collection or
   the CertiGC C code.  The current draft introduces function names such as
   `forward_remset`, `mutable_update`, and `do_generation` before giving enough
   operational background.

2. Explain the proof architecture earlier and more explicitly.  The reader
   should first learn that a VST proof relates the C collector to a functional
   graph model, and that `gc_correct.v` proves the graph after collection is
   isomorphic to the live subset of the graph before collection.

3. Distinguish the trusted Rocq kernel from the untrusted but useful Codex
   assistant.  Phrases such as "the machine checker" are better than vague
   references to "the machine" when the point is proof checking.

4. Make the stale `no_backward_edge` issue more direct.  The specification
   audit found that the old premise made the main theorem too weak for mutable
   GC, and the repair removed an inappropriate and unnecessary premise rather
   than merely changing an "invariant route".

5. Clarify human versus Codex responsibility.  In particular, explain how much
   previous hand-written proof was preserved, what Codex recreated or repaired,
   and how the human understanding from the earlier phase guided Codex.

6. Add more ordinary GC background and citation support.  The comment suggests
   citing the relevant chapter of Jones and Lins for generational garbage
   collection background.

7. Tighten ambiguous wording.  Terms or phrases called out include
   "plausible proof script", "existing verification target compiled",
   "close reachability", and "route".

8. Keep dates and quantitative evidence together.  If April 29 is mentioned,
   other relevant dates should either also be mentioned in the same discussion
   or the date should be moved to the results/statistics section.

9. The repository evidence table should say "git commits", not "CertiGC
   commits".

10. Consider adding effort estimates that are not in the current transcript
    statistics: active human hours, and an order-of-magnitude estimate of how
    long the same work might have taken without Codex.

## Page-by-page comments

### C01. DONE. Page 1, highlight

Highlighted text: "The machine checker"

Comment: distinguish between the trustworthy Rocq kernel and the untrustworthy
but helpful Codex.  If the draft says only "the machine", the distinction is
unclear.

Suggested handling: keep using "Rocq kernel", "proof assistant kernel", or
"machine checker" when the point is trusted proof checking; use "Codex" when
the point is LLM assistance.

### C02. DONE. Page 1, highlight

Highlighted location: the introductory CertiGC background sentence around
"generational copying collector".

Comment text proposes adding that CertiGC was proved correct in 2018, but could
not support mutable references and updateable arrays, and inadvertently could
not support byte strings because the correctness specification for such objects
was too weak.

Suggested handling: if factually correct, expand the first CertiGC background
sentence so the reader knows what the old verified collector did and why the
mutable-GC branch matters.

Confidence note: the visible highlight appears on "collector"; the comment
itself is a proposed insertion rather than a normal explanatory note.

Resolution note: the paper now states the confirmed limitation for mutable
references and updateable arrays, but does not include the byte-string claim.

### C03. DONE. Page 1, caret insertion

Insertion location: paragraph beginning "The work began as a conventional human
proof effort."

Comment: insert "(to strengthen the implementation, specification, and proof
for mutable references)".

Suggested handling: revise the sentence to say what the earlier human proof
effort was trying to strengthen, instead of simply saying that it existed.

### C04. DONE. Page 1, caret insertion

Insertion location: after `forward_remset`.

Comment: insert "function to process the remembered set".

Suggested handling: first mention of `forward_remset` should define it in prose,
for example as the C function that processes remembered-set entries during
collection.

### C05. DONE. Page 1, highlight

Highlighted text: "plausible"

Comment: "plausible" may not be the right word.

Suggested handling: replace "not to obtain a plausible proof script" with a
more precise contrast, such as "not merely to obtain a script that checked
locally" or another phrase that avoids implying that proof scripts can be
plausible apart from the theorem they establish.

### C06. DONE. Page 1, highlight

Highlighted text: `do_generation`

Comment: the page refers to `forward_remset`, `mutable_update`, and
`do_generation`, but the reader will not know what these are.  The typical
reader is also unlikely to know how generational garbage collection works.

Suggested handling: move or add a compact GC and CertiGC-code orientation
before these function names become central.

Resolution note: the introduction now gives a compact operational orientation
before these names become central: generation collection, the mutator-side write
barrier, `mutable_update`, `forward_remset`, and `do_generation`.  It also
cross-references the labeled `do_generation` call-sequence listing.

### C07. DONE. Page 1, highlight

Highlighted text: "where the existing verification target compiled and the
final theorem had the intended shape."

Comment: unclear what "existing verification target compiled" means.  Does the
C code compile, or does the entire theorem check in Rocq?

Suggested handling: say explicitly whether the repository's Rocq build checked,
the relevant `.v` files compiled to `.vo`, or the final theorem checked.

### C08. DONE. Page 1, text note

Comment: How much of the previous hand proof from 2024--2025 was preserved?
Did Codex recreate the whole process?  If Codex recreated it, how much of the
understanding from the first round was needed to direct Codex?

Suggested handling: add a paragraph on continuity from the earlier human phase:
which definitions/specifications/proof files were already present, which parts
were repaired by Codex, and what human expertise remained necessary.

Resolution note: the introduction now states that Codex inherited the existing
definitions, specifications, and partially repaired proofs rather than
recreating them.  The repository-evidence table now reports the pre-Codex human
groundwork as 23 git commits with net +5316/-2113 in `CertiGC`, compared with
51 git commits and net +13340/-3557 in the Codex-assisted phase.

### C09. DONE. Page 1, text note

Comment: send the next draft to Tim Carstens as well; he will be interested.

Suggested handling: not a paper edit, but note for circulation.

Resolution note: this is treated as a non-paper circulation action; no paper
text change is needed.

### C10. DONE. Page 1, text note

Comment: the biggest overall comment is to reread from the viewpoint of a
reader who knows verification, knows something about AI, knows very little
about garbage collection, and knows nothing about this C program.

Suggested handling: use this as the main revision principle.  Background and
proof-task sections should not assume local CertiGC knowledge.

Resolution note: the introduction now gives a compact operational account of
generational collection, `mutable_update`, `forward_remset`, and
`do_generation` before these names drive the proof story.  The proof-task
section now opens with the VST/mathematical-layer bridge, explains the main
remembered-set variables around the theorem statement, and rewrites the
specification-audit discussion to give the natural-language dependency path
before listing local source names.

### C11. DONE. Page 2, strikeout

Marked text: "The main theorem compiled"

Suggested handling: avoid saying that a theorem "compiled" unless the intended
meaning is carefully explained.  The adjacent caret suggests replacing this
with "The machine-checked proof of the main theorem was completed".

### C12. DONE. Page 2, caret insertion

Insertion location: sentence about April 29, 2026.

Comment: "The machine-checked proof of the main theorem was completed".

Suggested handling: use this wording if the date remains in the text.

### C13. DONE. Page 2, highlight

Highlighted text: "April 29, 2026"

Comment: if one date is mentioned here, but not all other relevant dates, the
choice seems odd.  If the purpose is to discuss speed with AI, perhaps mention
dates only in that section.

Suggested handling: either remove this date from the introduction or move it
into the results/timeline discussion where the other dates are already present.

### C14. DONE. Page 2, caret insertion

Insertion location: after the sentence saying the heap was effectively
immutable from the collector's perspective.

Comment: explain that once a record cell was created, its fields could not be
updated, as appropriate for a pure functional language.  Therefore the old proof
could rely on the absence of old-to-young edges.

Suggested handling: make the old immutable setting concrete before introducing
why mutable updates break the old invariant.

### C15. DONE. Page 2, caret insertion

Insertion location: after "Mutable updates invalidate that invariant."

Comment: add examples such as impure functional languages like ML, or lazy
thunk update in Haskell.

Suggested handling: use these examples to explain why mutation matters in a
functional-language runtime.

### C16. DONE. Page 2, highlight

Highlighted text: "Generational collection"

Comment: cite the appropriate chapter of Jones and Lins on garbage collection
for this background.

Suggested handling: add a background citation for generational collection and
remembered sets.

### C17. DONE. Page 3, highlight

Highlighted text: "forwards remembered-set entries first"

Comment: the typical reader, who may know verification or AI but not copying
garbage collection, will not know what "forward" means.

Suggested handling: define forwarding before showing or discussing
`forward_remset`.  A short explanation should say that copying collection
copies a reachable object to the target generation and leaves or follows a
forwarding pointer so later references are redirected to the copied object.

### C18. DONE. Page 3, caret insertion

Insertion location: after the sentence introducing the ordinary heap condition.

Comment: insert "that does not even take the remembered-set as a parameter".

Suggested handling: when contrasting the ordinary graph/heap condition with
the remembered-set invariant, explicitly state that the former is independent
of the remembered set.

### C19. DONE. Page 3, highlight

Highlighted text:
`Definition no_unrecorded_backward_edge (g: LGraph) (rh: remset_heap) : Prop :=`

Comment: did the human or the AI write this predicate?

Suggested handling: state the division of labor around the predicate: Codex
proposed and first formalized the no-unrecorded-backward-edge predicate in the
interaction, while the human author judged that this was the right semantic
replacement for the old no-backward-edge premise.

Resolution note: the paper now states this division of labor next to the
predicate definition.

### C20. DONE. Page 3, highlight

Highlighted text: "remembered-set states"

Comment: if understood correctly, the section should first explain that the VST
proof relates C program states to abstract graphs called heaps.  Then the
distinction between remembered-set heaps and remembered-set states will be
understandable.

Suggested handling: add a short bridge before the formal theorem explanation:
VST speaks about concrete C states and separation-logic resources, while the
functional model and correctness theorem speak about abstract graph heaps.

Resolution note: the proof-task section now opens with this bridge and explains
the roles of remembered-set heaps (`rh`) and remembered-set states (`rmst`).

### C21. DONE. Page 4, highlight

Highlighted text: "close reachability"

Comment: "compute the closure of (?)"

Suggested handling: replace "close reachability" with clearer wording, such as
"compute the transitive closure of reachability from both program roots and
remembered locations", if that matches the intended technical content.

### C22. DONE. Page 4, caret insertion

Insertion location: the paragraph explaining that any remaining backward edge
in the resulting graph is still recorded.

Comment: insert "(in, or promoted into, some older generation that was not
collected this time)".

Suggested handling: clarify why a backward edge can remain after collection:
the relevant object may be in, or have been promoted into, an older generation
not collected in that collection step.

### C23. DONE. Page 4, caret insertion

Insertion location: just before or around the displayed preservation lemma
`do_generation_relation_no_unrecorded_backward_edge_reset`.

Comment: "(designed by the human expert (?) )"

Suggested handling: clarify authorship and design of the key invariant or lemma
shape.  The text should distinguish Codex proposing or formalizing
`no_unrecorded_backward_edge` from the human decision that this invariant is the
right replacement for the old no-backward-edge condition.

Confidence note: the visible caret is near "the following abridged shape"; the
comment likely asks who designed the key predicate/lemma, not just who wrote
the displayed code.

Resolution note: the paper now states near the preservation lemma that Codex
introduced the VST-facing reset-preservation lemma shape under the accepted
invariant, while the author reviewed its semantic role and later directed the
core-and-wrapper factoring.

### C24. DONE. Page 4, highlight

Highlighted text: "Only after `verif_do_generation.v` and
`verif_garbage_collect.v` compiled was it productive to repair `gc_correct.v`."

Comment: first explain the high-level structure of the proof.  A
`verif_garbage_collect` proof in Rocq with VST and CertiGraph proves that the C
program correctly implements a functional model expressed using directed
graphs; then a `gc_correct` proof in Rocq proves that the graph after garbage
collection is isomorphic to the live subset of the graph before garbage
collection.

Suggested handling: add this proof-architecture overview before discussing the
file-ordering workflow.

Resolution note: the proof-task section now begins with the two-layer proof
architecture before presenting the main theorem or the workflow ordering.

### C25. DONE. Page 5, caret insertion

Insertion location: after `make CertiGC/GCGraph.vo`.

Comment: add a shell-comment explanation, "# rebuild definitions and proofs
about the graph functional model".

Suggested handling: if the command block remains, annotate commands so readers
can see why each target matters.

### C26. DONE. Page 5, caret insertion

Insertion location: after `make CertiGC/gc_correct.vo`.

Comment: add "# rebuild proofs that the functional model preserves
(live-subset) graph isomorphism".

Suggested handling: explain that this target checks the mathematical
correctness layer.

### C27. DONE. Page 5, caret insertion

Insertion location: after `make CertiGC/verif_garbage_collect.vo`.

Comment: add "# rebuild proofs that the C program implements the functional
model".

Suggested handling: explain that this target checks the VST-facing C-program
verification layer.

### C28. DONE. Page 5, caret insertion

Insertion location: after "The machine checker".

Comment: insert "(the Rocq kernel)".

Suggested handling: make the trusted checker explicit when explaining the
workflow feedback mechanism.

### C29. DONE. Page 5, caret insertion

Insertion location: "insert `Show` commands".

Comment: insert "ing".

Suggested handling: repair the grammar, for example by writing "replay a proof
prefix while inserting `Show` commands".

### C30. DONE. Page 6, table 2 strikeout and caret

Marked text: "16 CertiGC commits; +5292/-2086"

Comment: replace "CertiGC" with "git".

Suggested handling: table evidence should say "16 git commits; +5292/-2086".

### C31. DONE. Page 6, table 2 strikeout and caret

Marked text: "51 CertiGC commits; +13340/-3557"

Comment: replace "CertiGC" with "git".

Suggested handling: table evidence should say "51 git commits; +13340/-3557".

### C32. DONE. Page 6, table 2 strikeout and caret

Marked text: "74 CertiGC commits; +17953/-4967"

Comment: replace "CertiGC" with "git".

Suggested handling: table evidence should say "74 git commits; +17953/-4967".

### C33. DONE. Page 6, highlight

Highlighted text: "adding stronger heap/spatial preconditions to pure
specifications"

Comment: unclear; maybe give an example and explain in a footnote.

Suggested handling: either explain the concrete bad escape hatch or remove the
abstract phrase.  The adjacent insertion note says the issue is especially
about not exposing remembered-set internals in the main theorem.

### C34. DONE. Page 6, caret insertion

Insertion location: after "exposing remembered-set internals in the statement."

Comment: insert "of the main theorem (which would be inappropriate because the
remembered set should be treated as private information to the g.c.
implementation, not visible to the client)."

Suggested handling: add this explanation, either in prose or as a footnote, if
the sentence remains.

### C35. DONE. Page 7, highlight

Highlighted text: "route" in "the stale `no_backward_edge` route in the
VST-facing proof"

Comment: "route" may not be the right word and is hard to understand.  Also ask
whether the stale `no_backward_edge` made the isomorphism theorem too weak to
be useful.  If so, say more clearly that the specification audit found the main
theorem too weak to be useful, and that this was corrected by removing an
inappropriate and unnecessary premise.

Suggested handling: replace "route" language throughout the paper with a more
direct explanation of the old premise path and why it was invalid for mutable
GC.

### C36. DONE. Page 8, caret insertion

Insertion location: before "Active hours" in Table 4.

Comment: insert "Codex ".

Suggested handling: rename the metric to "Codex active hours" or equivalent,
so it is not confused with active human hours.

### C37. DONE. Page 8, text note

Location: Table 4 and the paragraph below it.

Comment: Can active human hours be estimated?  Would they be basically the same
as wall-clock hours?  Can the table include an order-of-magnitude estimate of
how many wall-clock hours the human would have needed without Codex?

Suggested handling: this is probably not derivable from rollout logs alone.  If
included, it should be explicitly labeled as an author estimate rather than a
transcript-derived statistic.

Resolution note: active human hours and hypothetical human-only effort are not
reported, because the author cannot estimate them reliably from the available
evidence.

### C38. DONE. Page 9, highlight

Highlighted text: "Compilation" in "Compilation is not the end of validation."

Comment: "A completed machine-checked proof".

Suggested handling: revise the topic sentence to avoid the misleading
"compilation" wording, for example "A completed machine-checked proof is not
the end of validation."

### C39. DONE. Page 10, text note

Location: limitations/validation discussion of the stale immutable-collector
assumption.

Comment proposes a footnote: "This assumption was not sneakily added by Codex,
because our workflow would not have permitted that; instead, it was a property
of the previous correct theorem about a simpler garbage collector."

Suggested handling: consider adding a short clarification, but probably avoid
the informal word "sneakily" in the paper.  The substance is useful: the bad
assumption predated Codex and came from the earlier immutable collector proof,
not from an unchecked Codex weakening.

## Items needing author confirmation

1. DONE. State the confirmed limitation for mutable references and updateable
   arrays; omit the byte-string claim.

2. DONE. Report the pre-Codex human groundwork and clarify that Codex inherited
   existing definitions, specifications, and partially repaired proofs.

3. DONE. Do not add an estimated human-only time cost or active human hours.

4. DONE. Describe authorship as Codex proposing/formalizing the predicate and
   the author accepting it after semantic review as the right replacement for
   the old no-backward-edge premise.

5. DONE. Treat sending the next draft to Tim Carstens as a non-paper
   circulation action.
