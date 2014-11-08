Require Import Syntax.
Require Import Vars.

Module M := FMapAVL.Make(TID).

Definition taskmap := M.t prog.

Definition make : taskmap := M.empty prog.

Definition newTask (tm:taskmap) (t:tid) : taskmap :=
  M.add t pnil tm.

Definition In := @M.In prog.

Definition MapsTo := @M.MapsTo prog.

Definition add := @M.add prog.

