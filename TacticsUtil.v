Ltac r_auto := repeat auto.
Ltac apply_auto H := apply H; r_auto.
Ltac expand H := inversion H; clear H; subst.

(* From http://adam.chlipala.net/cpdt/html/Match.html *)
Ltac find_if :=
  match goal with
    | [ |- if ?X then _ else _ ] => destruct X
  end.

Ltac find_if_inside :=
  match goal with
    | [ |- context[if ?X then _ else _] ] => destruct X
  end.

