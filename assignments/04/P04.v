Require Export P03.


Definition for_plus (n : c_nat) (n' : c_nat) (X :Type)(f : X -> X) (x : X) :=
(n X f (n' X f x)).

(** Addition of two natural numbers: *)

Definition c_plus (n m : c_nat) : c_nat :=
  for_plus n m.


(** Multiplication: *)

Definition for_mult (n : c_nat) (m : c_nat) (X :Type)(f : X -> X) (x : X) :=
n X (m X f ) x.

Definition c_mult (n m : c_nat) : c_nat :=
  for_mult n m.

Example c_mult_1 : c_mult c_one c_one = c_one.
Proof. reflexivity. Qed.

Example c_mult_2 : c_mult c_zero (c_plus c_three c_three) = c_zero.
Proof. reflexivity. Qed.

(** Oct. 20 : You have to copy definition of c_plus here from P03.v. **)

Example c_mult_3 : c_mult c_two c_three = c_plus c_three c_three.
Proof.
reflexivity.
Qed.

