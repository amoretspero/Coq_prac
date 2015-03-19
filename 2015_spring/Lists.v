Require Export Induction .
Module NatList .

Inductive natprod : Type :=
	pair : nat -> nat -> natprod .

Check (pair 3 5).

Definition fst (p : natprod) : nat :=
	match p with
	| pair x y => x
	end.

Definition snd (p : natprod) : nat :=
	match p with
	| pair x y => y
	end.

Eval compute in (fst (pair 3 5)).

Notation "x , y" := (pair x y) (at level 50, left associativity).