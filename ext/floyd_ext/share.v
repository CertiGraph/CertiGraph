Require Import VST.floyd.base.

Definition rshare: Type := sig (fun sh => readable_share sh).

Definition wshare: Type := sig (fun sh => writable_share sh).

Definition rshare_share (sh: rshare): share := proj1_sig sh.

Definition wshare_share (sh: wshare): share := proj1_sig sh.

Coercion rshare_share: rshare >-> share.

Coercion wshare_share: wshare >-> share.

Lemma rshare_readable: forall sh: rshare, readable_share sh.
Proof. intros [? ?]; simpl; auto. Qed.

Lemma wshare_writable: forall sh: wshare, writable_share sh.
Proof. intros [? ?]; simpl; auto. Qed.

Lemma wshare_readable: forall sh: wshare, readable_share sh.
Proof. intros [? ?]; simpl; auto. Qed.

Hint Resolve rshare_readable.
Hint Resolve wshare_writable.
Hint Resolve wshare_readable.
Identity Coercion share_share_t: share >-> Share.t.
