Require Import Coq.Structures.OrderedType.
Require Import Coq.FSets.FMapAVL.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Phaser.
Require Import Vars.

(* Define types *)
Import Map_PHID.
Definition phasermap := t phaser.

(* Define operations. *)
Definition make := empty phaser.
Definition newPhaser (pm:phasermap) (t:tid) (p:phid) : phasermap :=
  add p (Phaser.make t) pm.

Inductive op :=
  | NEW : phid -> op
  | APP : phid -> Phaser.op -> op.

Definition ph_apply (pm:phasermap) (t:tid) (p:phid) (o:Phaser.op) : phasermap :=
  match find p pm with
    | Some ph => add p (Phaser.apply ph t o) pm
    | None => pm
  end.

Definition apply (pm:phasermap) (t:tid) (o:op) : phasermap :=
  match o with
    | NEW p => newPhaser pm t p
    | APP p o' => ph_apply pm t p o'
  end.

