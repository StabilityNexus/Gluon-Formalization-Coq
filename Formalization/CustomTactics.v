Module CustomTactics.
	Ltac rewrite_vars_in H :=
	repeat match goal with
	| [ E: ?x = ?e |- _ ] =>
		first [
		rewrite E in H
		| rewrite <- E in H
		] 
	end.


End CustomTactics.