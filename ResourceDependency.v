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

(** We define a resource as a pair of phaser ids and a natural (the phase). *)
Module RES := PairOrderedType PHID Nat_as_OT.
Module Set_RES := FSetAVL.Make RES.
Module Set_RES_Extra := SetUtil Set_RES.
Module Map_RES := FMapAVL.Make RES.
Module Map_RES_Extra := MapUtil Map_RES.
Definition resource := RES.t.
Definition set_resource := Set_RES.t.
(*Definition res (p:phid) (n:nat) : resource := (p, n).*)

(* Function [get_phaser] obtains the phaser id in the resource. *)
Definition get_phaser (r:resource) : phid := fst r.

(* Function [get_phase] obtains the phase number of the resource. *)
Definition get_phase (r:resource) : nat := snd r.

(** Phases from the same phaser are in a precedes relation. *)
Definition prec (r1:resource) (r2:resource) :=
  get_phaser r1 = get_phaser r2 /\ get_phase r1 < get_phase r2.

Section StateProps.

Variable s:state.

(** We say that a task [t] is waiting for a resource [r] 
    when there is a task awaiting for a certain phase (which is represented by
    resource [r]). *)
Definition WaitsFor (t:tid) (r:resource) :=
  exists prg,
  Map_TID.MapsTo t (pcons (Await (get_phaser r) (get_phase r)) prg) (get_tasks s) /\
  Map_PHID.In (get_phaser r) (get_phasers s).

(** Since in our language tasks can only be blocked on a phase
    it is easy to see that the [WaitsFor] predicate is a function
    from task ids to resources. *)
Lemma waits_for_fun:
  forall t r r',
  WaitsFor t r ->
  WaitsFor t r' ->
  r = r'.
Proof.
  intros.
  unfold WaitsFor in *.
  destruct H as (p1, (H1, H2)).
  destruct H0 as (p2, (H3, H4)).
  (* MapsTo is functional, so p1 = p2 *)
  assert (Heq:= @Map_TID_Facts.MapsTo_fun _ _ _ _ _
          H1 H3).
  inversion Heq.
  destruct r as (p,n).
  destruct r' as (p', n').
  simpl in *.
  auto.
Qed.

(** We show that any task id in the [WaitsFor] is in the task map of [s]. *)
Lemma waits_for_in_tasks:
  forall t r,
  WaitsFor t r ->
  Map_TID.In t (get_tasks s).
Proof.
  intros.
  unfold WaitsFor in H.
  destruct H as (p, (H1, H2)).
  apply Map_TID_Extra.mapsto_to_in in H1.
  assumption.
Qed.

(** A task [t] is registered in a resource [r] if [t] is registered
    in phaser [get_phaser r] and in phase [get_phase r]; task [t] must
    be waiting for some resource. *)
Definition Registered (t:tid) (r:resource) :=
  exists ph,
  Map_PHID.MapsTo (get_phaser r) ph (get_phasers s) /\
  Map_TID.MapsTo t (get_phase r) ph /\ exists r', WaitsFor t r'.

(** Any registered task is waiting for some resource. *)
Lemma registered_to_blocked:
  forall t r,
  Registered t r ->
  exists r', WaitsFor t r'.
Proof.
  intros.
  unfold Registered in H.
  destruct H as (ph, (H1, (H2, H3))).
  assumption.
Qed.

(** A resource [r] impedes a task [r] if task [t] is registered in a
   preceeding resource; the impeding resource must be the target of
   a blocked task. *)
Definition Impedes (r:resource) (t:tid) :=
  (exists t', WaitsFor t' r) /\
  (exists r', Registered t r' /\ prec r' r).

Lemma impedes_def:
  forall r t t' r',
  WaitsFor t' r ->
  Registered t r' ->
  prec r' r ->
  Impedes r t.
Proof.
  unfold Impedes.
  intros.
  split.
  - exists t'.
    assumption.
  - exists r'.
    intuition.
Qed.

End StateProps.

(** We now characterize a deadlocked state.
    Let [AllTasksWaitFor] be a state such that all tasks in the state
    are waiting for a resource. *)

Definition AllTasksWaitFor s :=
  forall t, (Map_TID.In t (get_tasks s) -> exists r, WaitsFor s t r).

(** Let [AllBlockedRegistered] be a state such that any task waiting for
    a resource, that resource is also impeding another task in the state. *)

Definition AllImpedes s :=
  forall t r, WaitsFor s t r -> exists t', Impedes s r t'.

(** A totally deadlocked state is such that all tasks are waiting for
    resources that are impeding a tasks in the task map. *)

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

(** A GRG is defined as a bipartite graph *)
Definition GRG(s:state) := B.mk_bipartite _ _ (WaitsFor s) (Impedes s).
(** where if we contract the resources we get a WFG graph *)
Notation WFG s := (B.contract_a (GRG s)).
(** and where if we contract the tasks we get an SG graph *)
Notation SG s := (B.contract_b (GRG s)).
Notation TWalk s := (G.Walk (WFG s)).
Notation RWalk s := (G.Walk (SG s)).
Notation TCycle s := (G.Cycle (WFG s)).
Notation TEdge s := (G.Edge (WFG s)).
Notation RCycle s := (G.Cycle (SG s)).
Notation t_walk := (list (tid * tid) % type).

(** It is easy to see that if we have a WFG-edge, then there exists
    a resource [r] such that task [t1] is waiting for [r] and resource
    [r] impedes [t2]. *)
Lemma tedge_spec:
  forall s (t1 t2:tid),
  TEdge s (t1, t2) <->
  exists r,
  WaitsFor s t1 r /\ Impedes s r t2.
Proof.
  split.
  + intros.
    simpl in H.
    inversion H.
    subst.
    exists b.
    intuition.
  + intros.
    destruct H as (r, (H1, H2)).
    simpl.
    apply Core.aa with (b:=r); repeat auto.
Qed.

Section Dependencies.

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

End Dependencies.

Section Basic.
  Variable s:state.

Lemma impedes_in_tasks:
  forall r t,
  Impedes s r t ->
  Map_TID.In (elt:=prog) t (get_tasks s).
Proof.
  intros.
  destruct H as (_, (r', (H,_))).
  apply registered_to_blocked in H.
  destruct H as (r'', Hb).
  unfold WaitsFor in Hb.
  destruct Hb as (prg, (Hmt, _)).
  apply Map_TID_Extra.mapsto_to_in in Hmt.
  assumption.
Qed.

Lemma impedes_in_phasermap:
  forall r t,
  Impedes s r t ->
  Map_PHID.In (elt:=Phaser.phaser) (get_phaser r) (get_phasers s).
Proof.
  intros.
  destruct H as ((t',H),_).
  unfold WaitsFor in H.
  destruct H as (_, (_, H)).
  assumption.
Qed.

End Basic.