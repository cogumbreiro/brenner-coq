(* begin hide *)

Require Import
  Coq.Structures.OrderedTypeEx
  Coq.FSets.FSetAVL
  Coq.Arith.Compare_dec.

Require Import Aniceto.Set.
Require Import Aniceto.Map.

Require Import
  Brenner.Semantics TaskMap PhaserMap Vars Syntax.

Require Import Aniceto.Graphs.Graph.
Require Aniceto.Graphs.Bipartite.Bipartite.
Require Aniceto.Graphs.Bipartite.Cycle.

Set Implicit Arguments.

Module C := Graphs.Bipartite.Cycle.
(* end hide *)

(** We define an event as a pair of phaser ids and a natural (the phase). *)

Module EVT := PairOrderedType PHID Nat_as_OT.

(* begin hide *)
Module Set_EVT := FSetAVL.Make EVT.
Module Set_EVT_Extra := SetUtil Set_EVT.
Module Map_EVT := FMapAVL.Make EVT.
Module Map_EVT_Extra := MapUtil Map_EVT.
Definition set_event := Set_EVT.t.
(* end hide *)
Definition event := EVT.t.

(** Function [get_phaser] obtains the phaser id in the event. *)

Definition get_phaser (e:event) : phid := fst e.

(** Function [get_phase] obtains the phase number of the event. *)

Definition get_phase (e:event) : nat := snd e.

(** Phases from the same phaser are in a precedes relation. *)

Definition prec (e1:event) (e2:event) :=
  get_phaser e1 = get_phaser e2 /\ get_phase e1 < get_phase e2.

(* begin hide *)

Section StateProps.

Variable s:state.

(* end hide *)

(**
 
Let [s] be a [state].
We say that a task [t] is waiting for an event [e] 
when task [t] is executing an instruction [Await] and
the target phaser is defined in the phaser map. *)

Definition WaitsFor (t:tid) (e:event) :=
  exists prg,
  Map_TID.MapsTo t (pcons (Await (get_phaser e) (get_phase e)) prg) (get_tasks s) /\
  Map_PHID.In (get_phaser e) (get_phasers s).

(** A task [t] is registered in an event [e] if [t] is registered
    in phaser [get_phaser e] and in phase [get_phase r]; task [t] must
    be waiting for some event. *)

Definition Registered (t:tid) (e:event) :=
  exists ph,
  Map_PHID.MapsTo (get_phaser e) ph (get_phasers s) /\
  Map_TID.MapsTo t (get_phase e) ph /\ exists e', WaitsFor t e'.

(** an event [e] impedes a task [t] this task is registered in a
   event [e'] that precedes [e]; the impeding event must be the target of
   a blocked task. *)

Definition Impedes (e:event) (t:tid) :=
  (exists t', WaitsFor t' e) /\
  (exists e', Registered t e' /\ prec e' e).

Lemma impedes_def:
  forall e t t' e',
  WaitsFor t' e ->
  Registered t e' ->
  prec e' e ->
  Impedes e t.
Proof.
  unfold Impedes.
  intros.
  split.
  - exists t'.
    assumption.
  - exists e'.
    intuition.
Qed.


(** By inverting the impedes relation between [e] and [t] we have
    that there exists a task waiting for resource [e]. *)

Lemma impedes_inv_1:
  forall t e,
  Impedes e t ->
  exists e', WaitsFor t e'.
Proof.
  intros.
  destruct H as (_, (e', (H, _))).
  inversion H.
  intuition.
Qed.

End StateProps.

(** We now characterize a deadlocked state.
    Let [AllTasksWaitFor] be a state such that all tasks in the state
    are waiting for an event. *)

Definition AllTasksWaitFor s :=
  forall t, (Map_TID.In t (get_tasks s) -> exists e, WaitsFor s t e).

(** Let [AllBlockedRegistered] be a state such that any task waiting for
    an event, that event is also impeding another task in the state. *)

Definition AllImpedes s :=
  forall t e, WaitsFor s t e -> exists t', Impedes s e t'.

(** A totally deadlocked state is such that all tasks are waiting for
    events that are impeding a tasks in the task map. *)

Definition TotallyDeadlocked (s:state) :=
  AllTasksWaitFor s /\ AllImpedes s /\
  exists t, Map_TID.In t (get_tasks s). (* nonempty *)

(* TODO: Now would be a nice time to show that a totally deadlocked state
   does not reduce. For this we need to have a decidable reduction. *)

(** A [Deadlocked] state is such that we can take a partition of the task
    map [tm] and [tm'] such that the state [(get_phasers s, tm)] is
    totally deadlock. *)

Definition Deadlocked (s:state) :=
  exists tm tm',
  Map_TID_Props.Partition (get_tasks s) tm tm' /\
  TotallyDeadlocked ((get_phasers s), tm).

(** A GRG is a bipartite graph that is defined
   from relations [WaitsFor] and [Impedes]. *)

Notation TEdge s := (Bipartite.AA (WaitsFor s) (Impedes s)).
Notation REdge s := (Bipartite.BB (WaitsFor s) (Impedes s)).
Notation TWalk s := (Walk (TEdge s)).
Notation RWalk s := (Walk (REdge s)).
Notation TCycle s := (Cycle (TEdge s)).
Notation RCycle s := (Cycle (REdge s)).
Notation t_edge := (tid * tid) % type.
Notation t_walk := (list t_edge).

(** In WFG an arc from task [t1] to [t2] is read as [t1] waits for [t2].
    In Brenner this means that there exists an event [e] where task
    [t1] is blocked and task [t2] has not arrived at event [e].*)

Lemma tedge_spec:
  forall s (t1 t2:tid),
  TEdge s (t1, t2) <->
  exists e,
  WaitsFor s t1 e /\ Impedes s e t2.
Proof.
  split.
  + intros.
    simpl in H.
    inversion H.
    subst.
    exists b.
    intuition.
  + intros.
    destruct H as (e, (H1, H2)).
    simpl.
    eauto using Bipartite.aa.
Qed.

(** In an SG an arc from [e1] to [e2] can be read
    as event [e1] happens before event [e2].
    In Brenner, this means that there is a task [t]
    blocked in [e2] and impedes [e1]. Recall the definition
    of [Impedes] that states that [t] is registered in
    an event [e'] that precedes [e]; and that event
    [e] is obtained because there exists some task blocked
    in [e] (again by definition). *)

Lemma redge_spec:
  forall s (e1 e2:event),
  REdge s (e1, e2) <->
  exists t,
  Impedes s e1 t /\ WaitsFor s t e2.
Proof.
  split.
  - intros.
    inversion H.
    subst.
    exists a.
    simpl in *.
    intuition.
  - intros [t (Hi, Hw)].
    simpl.
    eauto using Bipartite.bb.
Qed.

Section Graphs.

Variable s:state.

(** Since the graph is bipartite, then if we have a cycle in the WFG, then
    there exists a cycle in the SG. *)

Theorem wfg_to_sg:
  forall s c,
  TCycle s c ->
  exists c', RCycle s c'.
Proof.
  intros.
  eauto using Cycle.cycle_a_to_b.
Qed.

(** Vice-versa also holds. *)

Theorem sg_to_wfg:
  forall c,
  RCycle s c ->
  exists c', TCycle s c'.
Proof.
  intros.
  eauto using Cycle.cycle_b_to_a.
Qed.

End Graphs.

Section Basic.
  Variable s:state.

(** In our language tasks can only await a single phaser, so
    it is easy to see that the [WaitsFor] predicate is actually a function
    from task ids to events. *)

Lemma waits_for_fun:
  forall t e e',
  WaitsFor s t e ->
  WaitsFor s t e' ->
  e = e'.
Proof.
  intros.
  unfold WaitsFor in *.
  destruct H as (p1, (H1, H2)).
  destruct H0 as (p2, (H3, H4)).
  (* MapsTo is functional, so p1 = p2 *)
  assert (Heq:= @Map_TID_Facts.MapsTo_fun _ _ _ _ _
          H1 H3).
  inversion Heq.
  destruct e as (p,n).
  destruct e' as (p', n').
  simpl in *.
  auto.
Qed.

(** We show that any task id in the [WaitsFor] is in the task map of [s]. *)

Lemma waits_for_in_tasks:
  forall t e,
  WaitsFor s t e ->
  Map_TID.In t (get_tasks s).
Proof.
  intros.
  unfold WaitsFor in H.
  destruct H as (p, (H1, H2)).
  apply Map_TID_Extra.mapsto_to_in in H1.
  assumption.
Qed.

(** Any registered task is waiting for some event. *)

Lemma registered_to_blocked:
  forall t e,
  Registered s t e ->
  exists e', WaitsFor s t e'.
Proof.
  intros.
  unfold Registered in H.
  destruct H as (ph, (H1, (H2, H3))).
  assumption.
Qed.

Lemma impedes_in_tasks:
  forall e t,
  Impedes s e t ->
  Map_TID.In (elt:=prog) t (get_tasks s).
Proof.
  intros.
  destruct H as (_, (e', (H,_))).
  apply registered_to_blocked in H.
  destruct H as (e'', Hb).
  unfold WaitsFor in Hb.
  destruct Hb as (prg, (Hmt, _)).
  apply Map_TID_Extra.mapsto_to_in in Hmt.
  assumption.
Qed.

Lemma impedes_in_phasermap:
  forall e t,
  Impedes s e t ->
  Map_PHID.In (elt:=Phaser.phaser) (get_phaser e) (get_phasers s).
Proof.
  intros.
  destruct H as ((t',H),_).
  unfold WaitsFor in H.
  destruct H as (_, (_, H)).
  assumption.
Qed.

End Basic.
