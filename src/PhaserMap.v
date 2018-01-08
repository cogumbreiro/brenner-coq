Require Import Coq.Structures.OrderedType.
Require Import Coq.FSets.FMapAVL.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Phaser.
Require Import Vars.

(** * Phaser map *)

(** A phaser map is a map from phaser identifier to a [phaser] state. *)

Import Map_PHID.
Definition phasermap := t phaser.

(** Function [make] creates an empty phasermap. *)

Definition make := empty phaser.

(** Function [newPhaser pm t p] expects a phaser map [pm] a task identifier [t]
  and a phaser identifier [p] and assigns a new phaser state to identifier [p];
  the phaser state is registered with task [t], as per [Phaser.make]. *)

Definition newPhaser (pm:phasermap) (t:tid) (p:phid) : phasermap :=
  add p (Phaser.make t) pm.

(** Thus, there are two possible operations, either we create a phaser
  with [NEW] or we invoke a phaser operation with [APP]. *)

Inductive op :=
  | NEW : phid -> op
  | APP : phid -> Phaser.op -> op.

(** Function [ph_apply pm t p o] looks up the phaser associated with
identifier [p] and applies a phaser operation [o] to that phaser, prefixed
with task [t]. *)

Definition ph_apply (pm:phasermap) (t:tid) (p:phid) (o:Phaser.op) : phasermap :=
  match find p pm with
    | Some ph => add p (Phaser.eval ph t o) pm
    | None => pm
  end.

(** The semantics can be summarized with operation [eval]. *)

Definition eval (pm:phasermap) (t:tid) (o:op) : phasermap :=
  match o with
    | NEW p => newPhaser pm t p
    | APP p o' => ph_apply pm t p o'
  end.

