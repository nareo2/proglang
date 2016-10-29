Require Export D.

Print rev.

(** **** Problem #13 : 3 stars (apply_exercise1)  *)
(** Hint: you can use [apply] with previously defined lemmas, not
    just hypotheses in the context.  Remember that [SearchAbout] is
    your friend. *)

Theorem app_nil_end : forall l : list nat, 
  l ++ [] = l.   
Proof.
  intros l.
  induction l as [|a b IHl].
  - reflexivity.
  - simpl. rewrite -> IHl.
    reflexivity.
Qed.  

Theorem rev_append : forall (l: list nat)( h : nat),
  rev( l ++ [h] )= h :: rev l.
Proof.
  intros l m.
  simpl.
  induction l as [|h t IHl].
  - reflexivity.
  - simpl.
    rewrite -> IHl.
    reflexivity.
Qed.
(** Hint: You may need to first state and prove some lemma about snoc and rev. *)
Theorem rev_involutive : forall l : list nat,
  rev (rev l) = l.
Proof.
  intros l.
  induction l as [| h t IHl'].
  - reflexivity.
  - simpl.
    rewrite -> rev_append.
    rewrite -> IHl'.
    reflexivity.
Qed.


Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
  intros l l'.
  intros H.
  rewrite -> H.
  rewrite -> rev_involutive.
  reflexivity.
Qed.

