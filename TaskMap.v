Require Import Syntax.
Require Import Vars.

Import Map_TID.

Definition taskmap := t prog.

Definition make : taskmap := empty prog.

Definition newTask (tm:taskmap) (t:tid) : taskmap :=
  add t pnil tm.

Definition In := @In prog.

Definition MapsTo := @MapsTo prog.

Definition add := @add prog.

