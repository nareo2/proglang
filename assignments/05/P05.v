Require Export P04.



Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X.
  intros P.
  intros Hf.
  unfold not.
  intros He.
  inversion He.
  apply H.
  apply Hf.
Qed.

