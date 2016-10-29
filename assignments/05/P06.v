Require Export P05.



Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X.
  intros P Q.
  unfold iff.
  split.
  - intros [x [Hl | Hr]].
    + left.
      exists x.
      apply Hl.
    + right.
      exists x.
      apply Hr.
  - intros [[x Hl] | [x Hr] ].
    + exists x.
      left.
      apply Hl.
    + exists x.
      right.
      apply Hr.
Qed.

