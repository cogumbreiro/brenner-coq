Require Import Coq.Structures.OrderedType.
Require Import Coq.FSets.FMapAVL.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Vars.

Import Map_TID.
(** * Phaser *)
(** A phaser is a map from tasks to phase numbers. *)

Definition phaser := t nat.

(** Operation advance increments the phase of the given task. *)

Definition advance (ph:phaser) (t:tid) : phaser :=
  match find t ph with
    | Some n => Map_TID.add t (n + 1) ph
    | None => ph
  end.

(** Operation await holds when every member of the phaser has
    reached at least phase [n]. *)

Definition await (ph:phaser) (n:nat) : Prop :=
  forall t n',
  MapsTo t n' ph ->
  n' <= n.

(** Operation [register] assigns a new member in the phaser. *)

Definition register (ph:phaser) (t:tid) (n:nat) : phaser :=
  add t n ph.

(** Operation [deregister] revokes the membership of a task in the phaser. *)

Definition deregister (ph:phaser) (t:tid) : phaser :=
  remove t ph.

(** Operation [phase] looks up the phase associated with a given task,
    or yields [None] if the given task  is unregistered. *)

Definition phase (ph:phaser) (t:tid) : option nat :=
  find t ph.

(** Creates a phaser with a given task initialized at phase [0]. *)

Definition make (t:tid) : phaser :=
  add t 0 (empty nat).

(** Defines the API of a phaser. *)

Inductive op :=
  | ADV : op
  | REG : tid -> op
  | DEREG : op.

(** Applies a phaser operation according to the tag. *)

Definition eval (ph:phaser) (t:tid) (o:op) : phaser :=
  match o with
    | ADV => advance ph t
    | REG t' =>
      match phase ph t with
        | Some n => register ph t' n
        | None => ph
      end
    | DEREG => deregister ph t
  end.
