Theorem plus_0_n : forall n : nat, 0 + n = n .
Proof.
	intros n.
	reflexivity.
Qed.

Theorem plus_n_0 : forall n : nat, n + 0 = n .
Proof.
	simpl.
Abort.

Theorem plus_1_l : forall n : nat, 1 + n = S n .
Proof.
	intros n .
	reflexivity.
Qed.

Theorem mult_0_l : forall n : nat, 0 * n = 0 .
Proof.
	intros n .
	reflexivity.
Qed.

Theorem plus_id_example : forall n m : nat, 
	n = m -> n + n = m + m
	.

Proof.
	intros n m .
	intros H .
	rewrite -> H .
	reflexivity. 
Qed.

Theorem plus_id_exercise : forall n m o : nat,
	n = m -> m = o -> n + m = m + o .
Proof.
	intros n m .
	intros H .
	intros Hn .
	intros Hm .
	rewrite -> Hn .
	rewrite -> Hm .
	reflexivity.
Qed.

Theorem mult_0_plus : forall n m : nat,
	(0 + n) * m = n * m .
Proof.
	intros .
	rewrite -> plus_0_n .
	reflexivity.
Qed.

Theorem mult_S_1 : forall n m : nat,
	m = S n -> m * (1 + n) = m * m .

Proof.
	intros.
	simpl.
	rewrite <- H .
	reflexivity.
Qed.