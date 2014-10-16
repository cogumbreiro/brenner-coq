Require Import Coq.Structures.OrderedType.
Require Import Coq.FSets.FMapAVL.

Module Phaser(TID:OrderedType).
Module M := FMapAVL.Make(TID).
Import M.
Definition phaser := t nat.
Definition tid := TID.t.

Definition advance (ph:phaser) (t:tid) : phaser :=
  match find t ph with
    | Some n => M.add t (n + 1) ph
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

End Phaser.

Module PhaserMap (PHID:OrderedType)(TID:OrderedType).

(* Define types *)
Module PH := Phaser(TID).
Module M := FMapAVL.Make(PHID).
Import M.
Definition phaser := PH.phaser.
Definition phasermap := t phaser.
Definition tid := TID.t.
Definition phid := PHID.t.
Definition phop := PH.op.

(* Define operations. *)
Definition make := empty phaser.
Definition newPhaser (pm:phasermap) (t:tid) (p:phid) : phasermap :=
  add p (PH.make t) pm.

Inductive op :=
  | NEWPH : phid -> op
  | APP : phid -> phop -> op.

Definition ph_apply (pm:phasermap) (t:tid) (p:phid) (o:phop) : phasermap :=
  match find p pm with
    | Some ph => add p (PH.apply ph t o) pm
    | None => pm
  end.

Definition apply (pm:phasermap) (t:tid) (o:op) : phasermap :=
  match o with
    | NEWPH p => newPhaser pm t p
    | APP p o' => ph_apply pm t p o'
  end.

End PhaserMap.

Module Brenner (PHID:OrderedType)(TID:OrderedType).

Module PM := PhaserMap PHID TID.

Definition tid := PM.tid.
Definition phid := PM.phid.
Definition pmop := PM.op.
Definition phop := PM.phop.
Definition phasermap := PM.phasermap.

Inductive prog :=
  | pcons : inst -> prog -> prog
  | pnil : prog
with inst :=
  | NewTid : tid -> inst
  | Fork : tid -> prog -> inst
  | PmOp: pmop -> inst
  | Await: phid -> nat -> inst
  | CFlow: cflow -> inst
with cflow :=
  | skip : cflow
  | loop : prog -> cflow.

Definition END := pnil.

Definition PMOP (o:pmop) :=
  pcons (PmOp o).

Definition PHAPP (ph:phid) (o:phop) :=
  PMOP (PM.APP ph o).

Definition DEREG (ph:phid) :=
  PHAPP ph PM.PH.DEREG.

Definition REG (ph:phid) (t:tid) :=
  PHAPP ph (PM.PH.REG t).

Definition ADV (ph:phid) :=
  PHAPP ph PM.PH.ADV.

Definition NEW_PHASER (p:phid) :=
  PMOP (PM.NEWPH p).

Definition NEW_TASK (t:tid) :=
  pcons (NewTid t).

Definition FORK (p:(tid*prog)%type) :=
  match p with
    | (t, b) => pcons (Fork t b)
  end.

Definition CFLOW (c:cflow) :=
  pcons (CFlow c).

Definition LOOP (b:prog) :=
  CFLOW (loop b).

Definition SKIP :=
  CFLOW skip.

Module TaskMap (TID':OrderedType).

  Module M := FMapAVL.Make(TID').
  Definition tid := TID'.t.
  Definition taskmap := M.t prog.
  Definition make : taskmap := M.empty prog.
  Definition newTask (tm:taskmap) (t:tid) : taskmap :=
    M.add t pnil tm.
  Definition In := @M.In prog.
  Definition MapsTo := @M.MapsTo prog.
  Definition add := @M.add prog.    
End TaskMap.

Module TM := TaskMap(TID).
Definition taskmap := TM.taskmap.

Definition state := (phasermap * taskmap) % type.

Fixpoint concat (p:prog) (q:prog) :=
  match p with
    | (pcons i p') => concat p' (pcons i q)
    | pnil => q
  end.

Inductive c_redex : cflow -> prog -> prog -> Prop :=
  | c_redex_skip:
    forall p,
    c_redex skip p p
  | c_redex_iter:
    forall p q,
    c_redex (loop p) q (concat p q)
  | c_redex_elide:
    forall p q,
    c_redex (loop p) q q.

Inductive s_redex: state -> state -> Prop :=
  | RNewTask :
    forall (t t':tid) (p:prog) (pm:phasermap) (tm:taskmap),
    TM.MapsTo t (NEW_TASK t' p) tm -> 
    ~ TM.In t' tm ->
    s_redex (pm, tm) (pm, TM.newTask tm t')
  | RFork :
    forall (t t':tid) (p p':prog) (pm:phasermap) (tm:taskmap),
    TM.MapsTo t (FORK(t', p') p) tm ->
    TM.MapsTo t' pnil tm ->
    s_redex (pm, tm) (pm, (TM.add t p (TM.add t' p' tm)))
  | RPhaser :
    forall (o:pmop) (t:tid) (p:prog) (pm:phasermap) (tm:taskmap),
    TM.MapsTo t (PMOP o p) tm ->
    s_redex (pm, tm) ((PM.apply pm t o), (TM.add t p tm))
  | RCFlow :
    forall t c p q pm tm,
    TM.MapsTo t (CFLOW c p) tm ->
    c_redex c p q ->
    s_redex (pm, tm) (pm, (TM.add t q tm)).
End Brenner.

Module Example1 (PHID:OrderedType)(TID:OrderedType).
Module B := Brenner PHID TID.
Import B.
Definition pm1 := PM.make.
Axiom t1 : tid.
Axiom ph1 : phid.
(* Definition bl : prog. *)
(* Definition bd := (pcons (CFlow loop bl) (pcons (PmOp ( *)
Definition p1 := NEW_PHASER ph1 END.
Definition tm1 := TM.add t1 p1 TM.make.
Definition s1 :state := (pm1, tm1).
Definition p1_1 := pnil.
Definition tm1_1 := TM.add t1 p1_1 tm1.
Definition pm1_1 := PM.apply PM.make t1 (PM.NEWPH ph1).
Definition s2 :state := (pm1_1, tm1_1).
Lemma t1_In_pm1 : TM.MapsTo t1 (NEW_PHASER ph1 pnil) tm1.
assert (H: TM.M.E.eq t1 t1).
apply (TM.M.E.eq_refl t1).
apply TM.M.add_1.
assumption.
Qed.

Goal s_redex s1 s2.
assert (H:=RPhaser (PM.NEWPH ph1) t1 pnil pm1 tm1 t1_In_pm1).
auto.


Qed.

