Require Export P07.



(** Recall that functions returning propositions can be seen as
    _properties_ of their arguments. For instance, if [P] has type
    [nat -> Prop], then [P n] states that property [P] holds of [n].

    Drawing inspiration from [In], write a recursive function [All]
    stating that some property [P] holds of all elements of a list
    [l]. To make sure your definition is correct, prove the [All_In]
    lemma below.  (Of course, your definition should _not_ just
    restate the left-hand side of [All_In].) *)

Fixpoint All {T} (P : T -> Prop) (l : list T) : Prop :=
match l with
| [] => True
| h :: t => (P h) /\ All P t
end.

Lemma All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
  intros T P .
  unfold iff.
  split.
  - intros Hx.
    induction l as [|h l' Hl'].
    + simpl.
      auto.
    + simpl.
      split.
      * simpl in Hx.
        apply Hx.
        left.
        reflexivity.
      * apply Hl'.
        intros x.
        intros H.
        apply Hx.
        simpl.
        right.
        apply H.
  - 
    induction l as [|h l' Hl'].
    + simpl.
      intros HA.
      intros x.
      intros HI.
      inversion HI.
    + simpl.
      intros HA.
      inversion HA.
      intros x.
      intros Ho.
      inversion Ho.
      * rewrite <- H1. apply H. 
      * apply Hl'.
        { apply H0. }
        { apply H1. }
Qed.
          
    