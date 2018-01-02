Require Import Vars.
Require Import PhaserMap.

(** Declares the language of a program. *)

Inductive prog :=
  | pcons : inst -> prog -> prog
  | pnil : prog
with inst :=
  | new_tid : tid -> inst
  | fork : tid -> prog -> inst
  | pm_op: PhaserMap.op -> inst
  | await: phid -> nat -> inst
  | c_op: cflow -> inst
with cflow :=
  | skip : cflow
  | loop : prog -> cflow.

Fixpoint concat (p:prog) (q:prog) :=
  match p with
    | pcons i p' => pcons i (concat p' q)
    | pnil => q
  end.

(** Declares a concrete syntax to simplify writing programs. *)

Module CST.

Notation "'END'" := (pnil).

Infix ";;" := pcons (at level 62, right associativity).

Notation "'DEREG' ( ph )" :=
  (pm_op (PhaserMap.APP ph Phaser.DEREG)) (at level 65).

Notation "'REG' ( ph , t )" :=
  (pm_op (PhaserMap.APP ph (Phaser.REG t))) (at level 65).

Notation "'ADV' ( ph ) " :=
  (pm_op (PhaserMap.APP ph Phaser.ADV)) (at level 65).

Notation "p '<-' 'NEW_PHASER'" :=
  (pm_op (PhaserMap.NEW p)) (at level 65).

Notation "t '<-' 'NEW_TID'" := (new_tid t) (at level 65).

Notation "'FORK' ( t , b ) " := (fork t b) (at level 65).


Notation "'CFLOW'" := c_op.

Notation "'LOOP' ( b )" := (c_op (loop b)). 

Notation "'SKIP'" := (CFLOW skip).

End CST.

