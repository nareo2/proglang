Require Export P01.



Example inversion_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  y :: l = x :: j ->
  y = z.
Proof. 
  intros X x y z l j.
  intros H.
  intros I.
  inversion H.
  inversion I.
  apply H1.
Qed.

