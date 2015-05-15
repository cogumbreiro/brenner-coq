Require Import
  Coq.Structures.OrderedTypeEx
  Coq.FSets.FSetAVL
  Coq.Arith.Compare_dec.

Require Import
  Semantics TaskMap PhaserMap Vars Syntax SetUtil MapUtil.

Require Graphs.Main.
Require Import Graphs.Core.
Require Graphs.Bipartite.Main.
Require Graphs.Bipartite.Cycle.

Set Implicit Arguments.

Module G := Graphs.Main.
Module B := Graphs.Bipartite.Main.
Module C := Graphs.Bipartite.Cycle.

Ltac r_auto := repeat auto.
Ltac apply_auto H := apply H; r_auto.

(** We define an event as a pair of phaser ids and a natural (the phase). *)
Module EVT := PairOrderedType PHID Nat_as_OT.
Module Set_EVT := FSetAVL.Make EVT.
Module Set_EVT_Extra := SetUtil Set_EVT.
Module Map_EVT := FMapAVL.Make EVT.
Module Map_EVT_Extra := MapUtil Map_EVT.
Definition event := EVT.t.
Definition set_event := Set_EVT.t.

(* Function [get_phaser] obtains the phaser id in the event. *)
Definition get_phaser (e:event) : phid := fst e.

(* Function [get_phase] obtains the phase number of the event. *)
Definition get_phase (e:event) : nat := snd e.

(** Phases from the same phaser are in a precedes relation. *)
Definition prec (r1:event) (r2:event) :=
  get_phaser r1 = get_phaser r2 /\ get_phase r1 < get_phase r2.

Section StateProps.

Variable s:state.

(** We say that a task [t] is waiting for an event [r] 
    when task [t] is executing an instruction [Await] and
    the target phaser is defined in the phaser map. *)
Definition WaitsFor (t:tid) (e:event) :=
  exists prg,
  Map_TID.MapsTo t (pcons (Await (get_phaser e) (get_phase e)) prg) (get_tasks s) /\
  Map_PHID.In (get_phaser e) (get_phasers s).

(** A task [t] is registered in an event [r] if [t] is registered
    in phaser [get_phaser r] and in phase [get_phase r]; task [t] must
    be waiting for some event. *)
Definition Registered (t:tid) (e:event) :=
  exists ph,
  Map_PHID.MapsTo (get_phaser e) ph (get_phasers s) /\
  Map_TID.MapsTo t (get_phase e) ph /\ exists e', WaitsFor t e'.

(** an event [r] impedes a task [t] this task is registered in a
   event [r'] that precedes [r]; the impeding event must be the target of
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
Definition GRG(s:state) := B.mk_bipartite _ _ (WaitsFor s) (Impedes s).
(** By contracting the events we get a WFG graph. *)
Notation WFG s := (B.contract_a (GRG s)).
(** By contracting the tasks we get an SG graph. *)
Notation SG s := (B.contract_b (GRG s)).

Notation TWalk s := (G.Walk (WFG s)).
Notation RWalk s := (G.Walk (SG s)).
Notation TCycle s := (G.Cycle (WFG s)).
Notation TEdge s := (G.Edge (WFG s)).
Notation REdge s := (G.Edge (SG s)).
Notation RCycle s := (G.Cycle (SG s)).
Notation t_walk := (list (tid * tid) % type).

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
    apply Core.aa with (b:=e); repeat auto.
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
    apply Core.bb with (a:=t); repeat auto.
Qed.

Section Graphs.

Variable s:state.
(** Since the graph is bipartite, then if we have a cycle in the WFG, then
    there exists a cycle in the SG. *)
Theorem wfg_to_sg:
  forall c,
  TCycle s c ->
  exists c', RCycle s c'.
Proof.
  intros.
  assert (H':= C.cycle_a_to_cycle_b (GRG s) c H).
  tauto.
Qed.

(** Vice-versa also holds. *)
Theorem sg_to_wfg:
  forall c,
  RCycle s c ->
  exists c', TCycle s c'.
Proof.
  intros.
  assert (H':= C.cycle_b_to_cycle_a (GRG s) c H).
  tauto.
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
