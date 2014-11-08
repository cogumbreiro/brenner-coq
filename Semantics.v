Require Import Vars.
Require Import PhaserMap.
Require Import Phaser.
Require Import Syntax.
Require Import TaskMap.

Definition state := (phasermap * taskmap) % type.

Import Syntax.CST.

Inductive c_redex : cflow -> prog -> prog -> Prop :=
  | RSkip:
    forall p,
    c_redex skip p p
  | RIter:
    forall p q,
    c_redex (loop p) q (concat p (LOOP(p);; q))
  | RElide:
    forall p q,
    c_redex (loop p) q q.

Inductive s_redex: state -> state -> Prop :=
  | RNewTask :
    forall (t t':tid) (p:prog) (pm:phasermap) (tm:taskmap),
    TaskMap.MapsTo t (t' <- NEW_TID;; p) tm -> 
    ~ TaskMap.In t' tm ->
    s_redex (pm, tm) (pm, newTask tm t')
  | RFork :
    forall (t t':tid) (p p':prog) (pm:phasermap) (tm:taskmap),
    TaskMap.MapsTo t (FORK(t', p');; p) tm ->
    TaskMap.MapsTo t' pnil tm ->
    s_redex (pm, tm) (pm, (TaskMap.add t p (TaskMap.add t' p' tm)))
  | RPhaser :
    forall (o:PhaserMap.op) (t:tid) (p:prog) (pm:phasermap) (tm:taskmap),
    TaskMap.MapsTo t ((PmOp o) ;; p) tm ->
    s_redex (pm, tm) ((PhaserMap.apply pm t o), (TaskMap.add t p tm))
  | RCFlow :
    forall t c p q pm tm,
    TaskMap.MapsTo t (CFLOW c;; p) tm ->
    c_redex c p q ->
    s_redex (pm, tm) (pm, (TaskMap.add t q tm)).

Definition load (t:tid) (b:prog) := (PhaserMap.make, TaskMap.add t b TaskMap.make).

(* Naive substitution, does not replace names in newphaser. *)

Fixpoint phid_subst (o_ph:phid) (n_ph:phid) (b:prog) :=
  let subst := phid_subst o_ph n_ph in
  match b with
    | pcons i b' =>
      let rest := subst b' in
      let same := i ;; rest in
      match i with
        | PmOp mo => 
          match mo with
            | PhaserMap.NEW ph =>
              if PHID.eq_dec o_ph ph
              then b
              else same
            | PhaserMap.APP ph o =>
              if PHID.eq_dec o_ph ph
              then PmOp (PhaserMap.APP n_ph o) ;; rest
              else same
          end
        | Fork t p => Fork t (subst p) ;; rest
        | CFlow c =>
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
        | NewTid t =>
          if TID.eq_dec o_t t
          then b (* no substitution *)
          else same
        | Fork t p => 
          if TID.eq_dec o_t t
          then Fork n_t (subst p) ;; kont
          else Fork t (subst p) ;; kont
        | PmOp po =>
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
        | CFlow c =>
          match c with
            | loop p => LOOP (subst p) ;; kont
            | skip => same
          end
        | _ => same
      end
    | END => END
  end.
