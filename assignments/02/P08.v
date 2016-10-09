Require Export P07.

Lemma rev_snoc : forall (h : nat) (t: natlist),
  rev ( snoc t h) = h :: rev(t).
Proof.
  intros h t.
  induction t as[|h' t' IHt'].
  - reflexivity.
  - simpl. rewrite -> IHt'. 
    reflexivity.
Qed.

(** Hint: You may need to first state and prove some lemma about snoc and rev. *)
Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intros l.
  induction l as [| h t IHl'].
  - reflexivity.
  - simpl. rewrite -> rev_snoc.
    rewrite -> IHl'.
    reflexivity.
Qed.



