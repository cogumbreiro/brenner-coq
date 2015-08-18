Require Import Coq.Structures.OrderedType.
Require Import Coq.FSets.FMapAVL.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Vars.

Import Map_TID.

Definition phaser := t nat.

Definition advance (ph:phaser) (t:tid) : phaser :=
  match find t ph with
    | Some n => Map_TID.add t (n + 1) ph
    | None => ph
  end.

Definition await (ph:phaser) (n:nat) : Prop :=
  forall t n',
  MapsTo t n' ph ->
  n' <= n.

Definition register (ph:phaser) (t:tid) (n:nat) : phaser :=
  add t n ph.

Definition deregister (ph:phaser) (t:tid) : phaser :=
  remove t ph.

Definition phase (ph:phaser) (t:tid) : option nat :=
  find t ph.

Definition make (t:tid) : phaser :=
  add t 0 (empty nat).

Inductive op :=
  | ADV : op
  | REG : tid -> op
  | DEREG : op.

Definition apply (ph:phaser) (t:tid) (o:op) : phaser :=
  match o with
    | ADV => advance ph t
    | REG t' =>
      match phase ph t with
        | Some n => register ph t' n
        | None => ph
      end
    | DEREG => deregister ph t
  end.
