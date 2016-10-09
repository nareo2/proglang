Require Export P09.

Lemma snoc_app : forall (a b : natlist) (h : nat),
  snoc ( a ++ b) h = a ++ snoc b h.
Proof.
  intros a b h.
  induction a as [|h' t' IHa].
  - reflexivity.
  - simpl. rewrite -> IHa. 
    reflexivity.
Qed.

Theorem distr_rev : forall l1 l2 : natlist,
  rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
  intros l1 l2.
  induction l1 as [|h t IH1].
  - simpl. rewrite -> app_nil_end.
    reflexivity.
  - simpl. rewrite -> IH1. 
    rewrite -> snoc_app.
    reflexivity.
Qed.

