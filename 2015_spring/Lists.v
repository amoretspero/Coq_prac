(*Require Export Induction.
Module NatList.*)
(* When Using Coqtop, those Module declaration cannot be used with query commands such as Print, Check, etc. *)

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

Notation "( x , y )" := (pair x y).

Eval compute in (fst (3, 5)).

Definition fst1 (p : natprod) : nat :=
	match p with
	| (x, y) => x
	end.

Definition snd1 (p : natprod) : nat :=
	match p with
	| (x, y) => y
	end.

Definition swap_pair (p : natprod) : natprod :=
	match p with
	| (x, y) => (y, x)
	end.

Theorem surjective_pairing1 : forall (n m : nat),
	(n, m) = (fst (n, m), snd (n, m)).
Proof.
	intros.
	simpl.
	reflexivity.
Qed.

Theorem surjective_pairing : forall (p : natprod),
	p = (fst p, snd p).
Proof.
	intros.
	destruct p as [n m].
	simpl.
	reflexivity.
Qed.

Theorem snd_fst_is_swap : forall (p : natprod),
	(snd p, fst p) = swap_pair p .
Proof.
	intros.
	destruct p as [n1 n2].
	simpl.
	reflexivity.
Qed.

Theorem fst_swap_is_snd : forall (p : natprod),
	fst (swap_pair p) = snd p 
	.
Proof.
	intros.
	destruct p .
	simpl.
	reflexivity.
Qed.

Inductive natlist : Type :=
	| nil : natlist
	| cons : nat -> natlist -> natlist
	.

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil .
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil .
Definition mylist3 := [1; 2; 3].

Fixpoint repeat (n count : nat) : natlist :=
	match count with
	| O => nil
	| S count' => n :: (repeat n count')
	end.

Fixpoint length (l : natlist) : nat :=
	match l with
	| nil => O
	| h :: t => S (length t)
  	end.

Fixpoint append (l1 l2 : natlist) : natlist :=
	match l1 with
	| nil => l2
	| h :: t => h :: (append t l2)
	end.

Notation "x ++ y" := (append x y) (right associativity, at level 60).

Example test_app1 : [1; 2; 3] ++ [4; 5] = [1; 2; 3; 4; 5].
Proof.
	simpl.
	reflexivity.
Qed.

Example test_app2 : nil ++ [4; 5] = [4; 5].
Proof.
	reflexivity.
Qed.

Example test_app3 : [1; 2; 3] ++ nil = [1; 2; 3].
Proof.
	simpl.
	reflexivity.
Qed.

Definition hd (default : nat) (l : natlist) : nat :=
	match l with
	| nil => default
	| h :: t => h
	end.

Definition tl (l : natlist) : natlist :=
	match l with
	| nil => nil
	| h :: t => t
	end.

Example test_hd1 : hd 0 [1; 2; 3] = 1.
Proof.
	simpl.
	reflexivity.
Qed.

Example test_hd2 : hd 0 [] = 0.
Proof.
	simpl.
	reflexivity.
Qed.

Example test_tl : tl [1; 2; 3] = [2; 3].
Proof.
	simpl.
	reflexivity.
Qed.

Fixpoint nonzeros (l : natlist) : natlist :=
	match l with
	| nil => nil
	| h :: t =>
		match h with
		| O => nonzeros t
		| p => p :: (nonzeros t)
		end
	end.

Example test_nonzeros : nonzeros [0; 1; 2; 3; 0; 0] = [1; 2; 3].
Proof.
	simpl.
	reflexivity.
Qed.

Fixpoint Is_odd (n : nat) : bool :=
	match n with
	| O => false
	| 1 => true
	| S (S p) => (Is_odd p)
	end.

Fixpoint oddmembers (l : natlist) : natlist :=
	match l with
	| nil => nil
	| h :: t =>
		if (Is_odd h) then 
			h :: (oddmembers t)
		else
			oddmembers t
	end.

Example test_oddmembers : oddmembers [0; 1; 2; 3; 0; 0] = [1; 3].
Proof.
	simpl.
	reflexivity.
Qed.

Fixpoint countoddmembers (l : natlist) : nat :=
	match l with
	| nil => O
	| h :: t =>
		match (Is_odd h) with
		| true => 1 + (countoddmembers t)
		| false => (countoddmembers t)
		end
	end.

Example test_countoddmembers1 : countoddmembers [1; 0; 3; 1; 4; 5] = 4.
Proof.
	reflexivity.
Qed.

Example test_countoddmembers2 : countoddmembers [0; 2; 4] = 0.
Proof.
	simpl.
	reflexivity.
Qed.

Example test_countoddmembers3 : countoddmembers nil = 0.
Proof.
	simpl.
	reflexivity.
Qed.