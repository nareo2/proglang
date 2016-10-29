Require Export P02.


Definition for_plus (n : c_nat) (n' : c_nat) (X :Type)(f : X -> X) (x : X) :=
(n X f (n' X f x)).

(** Addition of two natural numbers: *)

Definition c_plus (n m : c_nat) : c_nat :=
  for_plus n m.

Example c_plus_1 : c_plus c_zero c_one = c_one.
Proof. reflexivity. Qed.

Example c_plus_2 : c_plus c_two c_three = c_plus c_three c_two.
Proof. reflexivity. Qed.

Example c_plus_3 :
  c_plus (c_plus c_two c_two) c_three = c_plus c_one (c_plus c_three c_three).
Proof. reflexivity. Qed.

