Require Export P02.



Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q.
  intros H.
  unfold not.
  intros H2.
  intros HP.
  apply H2.
  apply H.
  apply HP.
Qed.

