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

Notation "'END'" := (pnil).

Infix ";;" := pcons (at level 62, right associativity).

Notation "'DEREG' ( ph )" :=
  (PmOp (PM.APP ph PM.PH.DEREG)) (at level 65).

Notation "'REG' ( ph , t )" :=
  (PmOp (PM.APP ph (PM.PH.REG t))) (at level 65).

Notation "'ADV' ( ph ) " :=
  (PmOp (PM.APP ph PM.PH.ADV)) (at level 65).

Notation "p '<-' 'NEW_PHASER'" :=
  (PmOp (PM.NEWPH p)) (at level 65).

Notation "t '<-' 'NEW_TID'" := (NewTid t) (at level 65).

Notation "'FORK' ( t , b ) " := (Fork t b) (at level 65).


Notation "'CFLOW'" := CFlow.

Notation "'LOOP' ( b )" := (CFlow (loop b)). 

Notation "'SKIP'" := (CFLOW skip).

Module TaskMap (TID':OrderedType).
  Require Import Coq.FSets.FMapFacts.
  Module M := FMapAVL.Make(TID').
  (* Utility lemmas about equals, in and so on. *)
  Module FACTS := WFacts_fun TID' M.
  (* Results about fold, elements, induction principles... *)
  Module PROPS := WProperties_fun TID' M.
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
    | pcons i p' => pcons i (concat p' q)
    | pnil => q
  end.

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
    TM.MapsTo t (t' <- NEW_TID;; p) tm -> 
    ~ TM.In t' tm ->
    s_redex (pm, tm) (pm, TM.newTask tm t')
  | RFork :
    forall (t t':tid) (p p':prog) (pm:phasermap) (tm:taskmap),
    TM.MapsTo t (FORK(t', p');; p) tm ->
    TM.MapsTo t' pnil tm ->
    s_redex (pm, tm) (pm, (TM.add t p (TM.add t' p' tm)))
  | RPhaser :
    forall (o:pmop) (t:tid) (p:prog) (pm:phasermap) (tm:taskmap),
    TM.MapsTo t ((PmOp o) ;; p) tm ->
    s_redex (pm, tm) ((PM.apply pm t o), (TM.add t p tm))
  | RCFlow :
    forall t c p q pm tm,
    TM.MapsTo t (CFLOW c;; p) tm ->
    c_redex c p q ->
    s_redex (pm, tm) (pm, (TM.add t q tm)).

Definition load (t:tid) (b:prog) := (PM.make, TM.add t b TM.make).
End Brenner.

Module Example1.
Require Import Coq.Structures.OrderedTypeEx.

Definition tid := nat.
Definition phid := nat.

Module B := Brenner Nat_as_OT Nat_as_OT.
Import B.

Definition t1 := 1.
Definition td := 2.
Definition ph1 := 1.
Parameter bf : prog.

Definition bl := t1 <- NEW_TID;; REG(ph1, t1);; FORK(t1, bf);; END.
Definition bd := LOOP(bl) ;; DEREG(ph1);; END.
Definition b := ph1 <- NEW_PHASER;; bd.
Definition s1_tm := TM.add td b TM.make.

(* The initial state uses the load function. *)
Definition s1 := load td b.

Definition s2_td := bd.
Definition s2_tm := TM.add td s2_td s1_tm.
Definition s2_pm := PM.apply PM.make td (PM.NEWPH ph1).
Definition s2 :state := (s2_pm, s2_tm).
Lemma td_In_s1_tm : TM.MapsTo td b s1_tm.
assert (H: TM.M.E.eq td td).
apply (TM.M.E.eq_refl td).
apply TM.M.add_1.
assumption.
Qed.

Goal s_redex s1 s2.
assert (H:=RPhaser (PM.NEWPH ph1) td bd PM.make s1_tm td_In_s1_tm).
auto.
Qed.

Definition s3_td := t1 <- NEW_TID;; REG(ph1, t1);; FORK(t1, bf);; bd.
Definition s3_tm := TM.add td s3_td s2_tm.
Definition s3_pm := s2_pm.
Definition s3 :state := (s3_pm, s3_tm).

Goal s_redex s2 s3.
apply RCFlow with (c:=loop bl) (p:=DEREG(ph1);; END).
unfold s2_tm.
unfold s2_td.
unfold bd.
apply TM.M.add_1.
apply (TM.M.E.eq_refl td).
apply RIter with (p:=bl) (q:=((DEREG  (ph1));; END)).
Qed.
