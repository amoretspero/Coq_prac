Require Import Omega.

Fixpoint sum (n: nat) : nat :=
	match n with
	| 0 => 0
	| S m => sum m + n
	end.

Eval compute in (sum 5).
Eval compute in (sum 6).