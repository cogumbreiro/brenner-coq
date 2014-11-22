Ltac r_auto := repeat auto.
Ltac apply_auto H := apply H; r_auto.
Ltac expand H := inversion H; clear H; subst.


