Inductive nat : Type :=
  | O : nat
  | S : nat -> nat
  .

Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day
  .

Definition next_weekday (d : day) : day :=
	match d with
	| monday => tuesday
	| tuesday => wednesday
	| wednesday => thursday
	| thursday => friday
	| friday => saturday
	| saturday => sunday
	| sunday => monday
	end.

Eval compute in (next_weekday friday).
Eval compute in (next_weekday (next_weekday saturday)).

Example test_next_weekday :
	(next_weekday (next_weekday saturday)) = monday
    .
    
Proof. 
	auto.
Qed.

Print test_next_weekday.

Inductive bool : Type :=
	| true : bool
	| false : bool.

Definition negb (b:bool) : bool :=
	match b with
	| true => false
	| false => true
	end.
Definition andb (b1:bool) (b2:bool) :=
	match b1 with
	| true => b2
	| false =>false
	end.
Definition orb (b1:bool) (b2:bool) : bool :=
	match b1 with
	| true => true
	| false => b2
	end.

Definition andb2 (b1:bool) (b2:bool):bool :=
	match b2 with
	| true => b1
	| false => false
	end.
Lemma andb_eq_andb2 : forall (b1 b2:bool),
	andb b1 b2 = andb2 b1 b2.
	
Proof.
	intros.
	destruct b1.
	- destruct b2.
		+ simpl. reflexivity. 
		+ simpl. reflexivity. 
	- destruct b2.
		+ simpl. reflexivity. 
		+ simpl. reflexivity.
Qed.

Print andb_eq_andb2.

Definition nand (b1:bool) (b2:bool):bool :=
	negb(andb b1 b2).

Fixpoint plus (n : nat) (m : nat) : nat :=
	match n with
	| O => m
	| S n' => S (plus n' m)
	end.

Lemma add_assoc_n_Sn: forall n : nat,
	(forall m k : nat, plus n (plus m k) = plus (plus n m) k)
	->
	(forall m k : nat, plus (S n) (plus m k) = plus (plus (S n) m) k).

Proof.
	intros n.
	intros Hn.
	intros m.
	intros k.

	simpl plus at 1.
	simpl plus at 4.
	simpl plus at 3.

	specialize (Hn m k).
	rewrite Hn.
	reflexivity.
Qed.

Lemma add_assoc: forall (n m k : nat),
	plus n (plus m k) = plus (plus n m) k
	.

