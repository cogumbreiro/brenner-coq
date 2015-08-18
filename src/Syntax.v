Require Import Vars.
Require Import PhaserMap.
Inductive prog :=
  | pcons : inst -> prog -> prog
  | pnil : prog
with inst :=
  | NewTid : tid -> inst
  | Fork : tid -> prog -> inst
  | PmOp: PhaserMap.op -> inst
  | Await: phid -> nat -> inst
  | CFlow: cflow -> inst
with cflow :=
  | skip : cflow
  | loop : prog -> cflow.

Fixpoint concat (p:prog) (q:prog) :=
  match p with
    | pcons i p' => pcons i (concat p' q)
    | pnil => q
  end.

Module CST.

Notation "'END'" := (pnil).

Infix ";;" := pcons (at level 62, right associativity).

Notation "'DEREG' ( ph )" :=
  (PmOp (PhaserMap.APP ph Phaser.DEREG)) (at level 65).

Notation "'REG' ( ph , t )" :=
  (PmOp (PhaserMap.APP ph (Phaser.REG t))) (at level 65).

Notation "'ADV' ( ph ) " :=
  (PmOp (PhaserMap.APP ph Phaser.ADV)) (at level 65).

Notation "p '<-' 'NEW_PHASER'" :=
  (PmOp (PhaserMap.NEW p)) (at level 65).

Notation "t '<-' 'NEW_TID'" := (NewTid t) (at level 65).

Notation "'FORK' ( t , b ) " := (Fork t b) (at level 65).


Notation "'CFLOW'" := CFlow.

Notation "'LOOP' ( b )" := (CFlow (loop b)). 

Notation "'SKIP'" := (CFLOW skip).

End CST.

