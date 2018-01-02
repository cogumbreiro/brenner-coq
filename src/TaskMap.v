Require Import Syntax.
Require Import Vars.

Import Map_TID.

(** A task map is a map from task identifiers to programs. *)

Definition taskmap := t prog.

(** Function [make] creates an empty task map. *)

Definition make : taskmap := empty prog.

(** Function [newTask t tm] puts a task identifier [t] in the task map [tm] 
    initialized with an empty program. *)

Definition newTask (tm:taskmap) (t:tid) : taskmap :=
  add t pnil tm.

Definition In := @In prog.

Definition MapsTo := @MapsTo prog.

Definition add := @add prog.

