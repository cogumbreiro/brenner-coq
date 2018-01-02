Require Import Vars.
Require Import PhaserMap.
Require Import Phaser.
Require Import Syntax.
Require Import TaskMap.

(** A state pairs the state of all phasers and the state of all tasks. *)

Definition state := (phasermap * taskmap) % type.

Definition get_tasks (s:state) :taskmap := snd s.
Definition get_phasers (s:state) : phasermap := fst s.

Import Syntax.CST.

(** Control-flow reduction: *)

Module ControlFlow.
Inductive Reduces : cflow -> prog -> prog -> Prop :=
  | r_skip:
    forall p,
    Reduces skip p p
  | r_iter:
    forall p q,
    Reduces (loop p) q (concat p (LOOP(p);; q))
  | r_elide:
    forall p q,
    Reduces (loop p) q q.
End ControlFlow.

(** Small step semantics for states. *)

Inductive Reduces: state -> state -> Prop :=
  | r_new_task:
  (** Creates a new task. Task id [t'] must not be present in
      defined in the task map. *)
    forall (t t':tid) (p:prog) (pm:phasermap) (tm:taskmap),
    TaskMap.MapsTo t (t' <- NEW_TID;; p) tm -> 
    ~ TaskMap.In t' tm ->
    Reduces (pm, tm) (pm, newTask tm t')
  | r_fork:
    (** Fork assigns a program to an "empty" task. *)
    forall (t t':tid) (p p':prog) (pm:phasermap) (tm:taskmap),
    TaskMap.MapsTo t (FORK(t', p');; p) tm ->
    TaskMap.MapsTo t' pnil tm ->
    Reduces (pm, tm) (pm, (TaskMap.add t p (TaskMap.add t' p' tm)))
  | r_phaser:
    (** Invokes a phaser operation on a given phaser identifier. *)
    forall (o:PhaserMap.op) (t:tid) (p:prog) (pm:phasermap) (tm:taskmap),
    TaskMap.MapsTo t ((pm_op o) ;; p) tm ->
    Reduces (pm, tm) ((PhaserMap.eval pm t o), (TaskMap.add t p tm))
  | r_cflow:
    (** Runs a control-flow operation. *)
    forall t c p q pm tm,
    TaskMap.MapsTo t (CFLOW c;; p) tm ->
    ControlFlow.Reduces c p q ->
    Reduces (pm, tm) (pm, (TaskMap.add t q tm)).

(** Creates a new state from a given program. *)

Definition load (t:tid) (b:prog) := (PhaserMap.make, TaskMap.add t b TaskMap.make).

(* begin hide *)

(* Naive substitution, does not replace names in newphaser. *)

Fixpoint phid_subst (o_ph:phid) (n_ph:phid) (b:prog) :=
  let subst := phid_subst o_ph n_ph in
  match b with
    | pcons i b' =>
      let rest := subst b' in
      let same := i ;; rest in
      match i with
        | pm_op mo => 
          match mo with
            | PhaserMap.NEW ph =>
              if PHID.eq_dec o_ph ph
              then b
              else same
            | PhaserMap.APP ph o =>
              if PHID.eq_dec o_ph ph
              then pm_op (PhaserMap.APP n_ph o) ;; rest
              else same
          end
        | fork t p => fork t (subst p) ;; rest
        | c_op c =>
          match c with
            | loop p => LOOP (subst p) ;; rest
            | skip => same
          end
        | _ => same
      end
    | END => END
  end.

Fixpoint tid_subst (o_t:tid) (n_t:tid) (b:prog) := 
  let subst := tid_subst o_t n_t in
  match b with
    | pcons i b' =>
      let kont := subst b' in
      let same := i ;; kont in
      match i with
        | new_tid t =>
          if TID.eq_dec o_t t
          then b (* no substitution *)
          else same
        | fork t p => 
          if TID.eq_dec o_t t
          then fork n_t (subst p) ;; kont
          else fork t (subst p) ;; kont
        | pm_op po =>
          match po with
            | PhaserMap.APP p o =>
              match o with
                | Phaser.REG t =>
                  if TID.eq_dec o_t t
                  then REG(p, n_t) ;; kont
                  else same
                | _ => same
              end
            | _ => same
          end
        | c_op c =>
          match c with
            | loop p => LOOP (subst p) ;; kont
            | skip => same
          end
        | _ => same
      end
    | END => END
  end.

(* end hide *)