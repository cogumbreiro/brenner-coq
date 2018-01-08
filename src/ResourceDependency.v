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

(** * Resource dependency state *)

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

Definition WaitOn (t:tid) (e:event) :=
  exists prg,
  Map_TID.MapsTo t (pcons (await (get_phaser e) (get_phase e)) prg) (get_tasks s) /\
  Map_PHID.In (get_phaser e) (get_phasers s).

(** A task [t] is registered in an event [e] if [t] is registered
    in phaser [get_phaser e] and in phase [get_phase r]; task [t] must
    defined in the taskmap. *)

Definition Registered (t:tid) (e:event) :=
  exists ph,
  Map_PHID.MapsTo (get_phaser e) ph (get_phasers s) /\
  Map_TID.MapsTo t (get_phase e) ph /\ Map_TID.In t (get_tasks s).

Lemma registered_def:
  forall ph e t,
  Map_PHID.MapsTo (get_phaser e) ph (get_phasers s) ->
  Map_TID.MapsTo t (get_phase e) ph ->
  Map_TID.In t (get_tasks s) ->
  Registered t e.
Proof.
  intros.
  unfold Registered.
  exists ph.
  intuition.
Qed.

Lemma registered_in_tasks:
  forall t e,
  Registered t e ->
  Map_TID.In t (get_tasks s).
Proof.
  unfold Registered.
  intros.
  destruct H as (?,(?,(?,?))).
  assumption.
Qed.

(** an event [e] impedes a task [t] this task is registered in a
   event [e'] that precedes [e]; the impeding event must be the target of
   a blocked task. *)

Definition ImpededBy(e:event) (t:tid) :=
  (exists t', WaitOn t' e) /\
  (exists e', Registered t e' /\ prec e' e).

Lemma impeded_by_def:
  forall e t t' e',
  WaitOn t' e ->
  Registered t e' ->
  prec e' e ->
  ImpededBy e t.
Proof.
  unfold ImpededBy.
  intros.
  split.
  - exists t'.
    assumption.
  - exists e'.
    intuition.
Qed.

Lemma impeded_by_in_tasks:
  forall t e,
  ImpededBy e t ->
  Map_TID.In t (get_tasks s).
Proof.
  intros.
  destruct H as (_,(?,(H,_))).
  eauto using registered_in_tasks.
Qed.

End StateProps.

(** We now characterize a deadlocked state.
    Let [AllTasksWaitFor] be a state such that all tasks in the state
    are waiting for an event. *)

Definition AllTasksWaitOn s :=
  forall t, (Map_TID.In t (get_tasks s) -> exists e, WaitOn s t e).

(** Let [AllBlockedRegistered] be a state such that any task waiting for
    an event, that event is also impeding another task in the state. *)

Definition AllImpededBy s :=
  forall t e, WaitOn s t e -> exists t', ImpededBy s e t'.

(** A totally deadlocked state is such that all tasks are waiting for
    events that are impeding a tasks in the task map. *)

Definition TotallyDeadlocked (s:state) :=
  AllTasksWaitOn s /\ AllImpededBy s /\
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
   from relations [WaitOn] and [ImpededBy]. *)

Notation TEdge s := (Bipartite.AA (WaitOn s) (ImpededBy s)).
Notation REdge s := (Bipartite.BB (WaitOn s) (ImpededBy s)).
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
  WaitOn s t1 e /\ ImpededBy s e t2.
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
    of [ImpededBy] that states that [t] is registered in
    an event [e'] that precedes [e]; and that event
    [e] is obtained because there exists some task blocked
    in [e] (again by definition). *)

Lemma redge_spec:
  forall s (e1 e2:event),
  REdge s (e1, e2) <->
  exists t,
  ImpededBy s e1 t /\ WaitOn s t e2.
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
    it is easy to see that the [WaitOn] predicate is actually a function
    from task ids to events. *)

Lemma wait_on_fun:
  forall t e e',
  WaitOn s t e ->
  WaitOn s t e' ->
  e = e'.
Proof.
  intros.
  unfold WaitOn in *.
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

(** We show that any task id in the [WaitOn] is in the task map of [s]. *)

Lemma wait_on_in_tasks:
  forall t e,
  WaitOn s t e ->
  Map_TID.In t (get_tasks s).
Proof.
  intros.
  unfold WaitOn in H.
  destruct H as (p, (H1, H2)).
  apply Map_TID_Extra.mapsto_to_in in H1.
  assumption.
Qed.

Lemma impeded_by_in_phasermap:
  forall e t,
  ImpededBy s e t ->
  Map_PHID.In (elt:=Phaser.phaser) (get_phaser e) (get_phasers s).
Proof.
  intros.
  destruct H as ((t',H),_).
  unfold WaitOn in H.
  destruct H as (_, (_, H)).
  assumption.
Qed.

End Basic.
