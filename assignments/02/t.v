Require Export P07.

fixpoint snoc (l : natlist) (v : nat) {struct l} : natlist :=
  match l with
  | [ ] => [v]
  | h :: t => h :: snoc t v
  end.