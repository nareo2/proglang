Require Export D.



(** **** Problem #7 : 2 stars (split) *)
(** The function [split] is the right inverse of combine: it takes a
    list of pairs and returns a pair of lists.  In many functional
    programing languages, this function is called [unzip].

    Uncomment the material below and fill in the definition of
    [split].  Make sure it passes the given unit tests. *)

Fixpoint app_list_pair 
          {X Y : Type} (l m : (list X)*(list Y) )
           : (list X) * (list Y):=
match l, m with
  | _ ,_ => ( (fst l ++ fst m ) , (snd l ++ snd m) )
end.
(*
Fixpoint split
           {X Y : Type} (l : list (X*Y))
           : (list X) * (list Y) :=
match l with
| [] => ([] , [])
| cons (h , h') t
=>match t with
  | [] => ( (h :: []), (h' :: []) )
  | cons (p, p') t' 
  => app_list_pair (( h :: p :: []),(h' :: p' ::[])) (split t')
  end
end.
*)
Fixpoint split
           {X Y : Type} (l : list (X*Y))
           : (list X) * (list Y) :=
match l with
| [] => ([],[])
| (h, h') :: t 
  => app_list_pair ((h :: []) , (h' :: [])) (split t)
end.


Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. simpl. reflexivity. Qed.

Theorem split_map: forall X Y (l: list (X*Y)),
   fst (split l) = map fst l.
Proof.
  intros X Y l.
  induction l as [|(h, h') t IHt].
  - reflexivity.
  - simpl.
    rewrite -> IHt.
    reflexivity.
Qed.

