Require Export P02.



Lemma plus_tech2 : forall n m,
  S( n + m) = n + S m.
Proof.
  intros n m.
  induction n as [|n' IHn].
  - reflexivity.
  - simpl. rewrite ->IHn.
    reflexivity.
Qed.
    
    

(** **** Problem : 2 stars (double_plus) *)

(* See [D.v] for the definition of [double] *)

(** Use induction to prove this simple fact about [double]: *)

Lemma double_plus : forall n, double n = n + n .
Proof.  
  intros n. induction n as [|n' IHn].
  - reflexivity.
  - simpl. rewrite -> IHn.
    rewrite -> plus_tech2.
    reflexivity.
Qed.


