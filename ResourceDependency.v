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
Module G := Graphs.Main.
Module B := Graphs.Bipartite.Main.
Module C := Graphs.Bipartite.Cycle.

Ltac r_auto := repeat auto.
Ltac apply_auto H := apply H; r_auto.

Module RES := PairOrderedType PHID Nat_as_OT.
Module Set_RES := FSetAVL.Make RES.
Module Set_RES_Extra := SetUtil Set_RES.
Module Map_RES := FMapAVL.Make RES.
Module Map_RES_Extra := MapUtil Map_RES.
Definition resource := RES.t.
Definition set_resource := Set_RES.t.
Definition res (p:phid) (n:nat) : resource := (p, n).
Definition get_phaser (r:resource) : phid := fst r.
Definition get_phase (r:resource) : nat := snd r.

(* Defines the module of I *)
Definition impedes := Map_RES.t set_tid.
Definition waits := Map_TID.t set_resource.
Definition dependencies := (impedes * waits) % type.
Definition get_waits (d:dependencies) : waits := snd d.
Definition get_impedes (d:dependencies) : impedes := fst d.

(* Phases from the same phaser are in a precedes relation. *)
Definition prec (r1:resource) (r2:resource) :=
  get_phaser r1 = get_phaser r2 /\ get_phase r1 < get_phase r2.

Section StateProps.

Variable s:state.

(* We say that a task [t] is blocked on a resource [r] if there exists a task in the
   task map that is awaiting on resource [r] and phaser [get_phaser r] is in the phaser map. *)
Definition WaitsFor (t:tid) (r:resource) :=
  exists prg,
  Map_TID.MapsTo t (pcons (Await (get_phaser r) (get_phase r)) prg) (get_tasks s) /\
  Map_PHID.In (get_phaser r) (get_phasers s).

(* It is easy to see that the blocked predicate is a function from task ids to resources. *)
Lemma blocked_fun:
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

(* Similarly, any blocked task is in the task map of [s]. *)
Lemma blocked_in_tasks:
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

(* A task [t] is registered in a resource [r] if [t] is registered
   in phaser [get_phaser r] and in phase [get_phase r]. We only
   consider registered tasks if they are blocked in some resource. *)
Definition Registered (t:tid) (r:resource) :=
  exists ph,
  Map_PHID.MapsTo (get_phaser r) ph (get_phasers s) /\
  Map_TID.MapsTo t (get_phase r) ph /\ exists r', WaitsFor t r'.

(* Again, any task registered in a resource is blocked on some resource. *)
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

(* We build the phaser map of waiting tasks to be constituted by all
   blocked tasks in state [s]. *)
Definition W_of (w:waits) := 
  forall t r,
  (exists rs, Map_TID.MapsTo t rs w /\ Set_RES.In r rs)
  <->
  WaitsFor t r.

(* A resource [r] blocks a task [r] if task [t] is registered in a
   preceeding resource. The resource that blocks must be target of
   a blocked task. *)
Definition Impedes (r:resource) (t:tid) :=
  (exists t', WaitsFor t' r) /\
  (exists r', Registered t r' /\ prec r' r).

Lemma blocks_def:
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

(* The map of impedes holds all resources that are blocking a task. *)
Definition I_of (i:impedes) := 
  forall t r,
  (exists ts, Map_RES.MapsTo r ts i /\ Set_TID.In t ts)
  <->
  Impedes r t.

Definition Deps_of (d:dependencies) :=
  W_of (get_waits d) /\ I_of (get_impedes d).

End StateProps.

Definition AllTasksBlocked s :=
  forall t, (Map_TID.In t (get_tasks s) -> exists r, WaitsFor s t r).

Definition AllBlockedRegistered s :=
  forall t r,
  WaitsFor s t r ->
  exists t',
  Map_TID.In t' (get_tasks s) /\ (exists r', Registered s t' r' /\ prec r' r).

Definition TotallyDeadlocked (s:state) :=
  AllTasksBlocked s /\ AllBlockedRegistered s /\
  exists t, Map_TID.In t (get_tasks s). (* nonempty *)

Definition Deadlocked (s:state) :=
  exists tm tm',
  Map_TID_Props.Partition (get_tasks s) tm tm' /\
  TotallyDeadlocked ((get_phasers s), tm).

Module T := PairOrderedType TID TID.
Module Set_T := FSetAVL.Make T.
Module Set_T_Props := FSetProperties.Properties Set_T.
Module Set_T_Facts := FSetFacts.Facts Set_T.
Module Map_T := FMapAVL.Make T.
Definition t_edge := T.t.
Definition set_t_edge := Set_T.t.

Module R := PairOrderedType RES RES.
Module Set_R := FSetAVL.Make R.
Module Map_R := FMapAVL.Make R.
Definition r_edge := R.t.
Definition set_r_edge := Set_R.t.

Definition WEdge (d:dependencies) (t:tid) (r:resource) :=
  exists rs, Map_TID.MapsTo t rs (get_waits d) /\ Set_RES.In r rs.

Definition IEdge (d:dependencies) (r:resource) (t:tid) :=
  exists ts, Map_RES.MapsTo r ts (get_impedes d) /\ Set_TID.In t ts.

Definition GRG(d:dependencies) := B.mk_bipartite _ _ (WEdge d) (IEdge d).

Notation WFG d := (B.contract_a (GRG d)).
Notation SG d := (B.contract_b (GRG d)).
Notation TWalk d := (G.Walk (WFG d)).
Notation RWalk d := (G.Walk (SG d)).
Notation TCycle d := (G.Cycle (WFG d)).
Notation TEdge d := (G.Edge (WFG d)).
Notation RCycle d := (G.Cycle (SG d)).
Notation t_walk := (list t_edge).

Lemma tedge_spec:
  forall d (t1 t2:tid),
  TEdge d (t1, t2) <->
  exists r,
  WEdge d t1 r /\ IEdge d r t2.
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

Variable d:dependencies.

Theorem wfg_to_sg:
  forall w,
  TCycle d w ->
  exists w', RCycle d w'.
Proof.
  intros.
  assert (H':= C.cycle_a_to_cycle_b (GRG d) w H).
  tauto.
Qed.

Theorem sg_to_wfg:
  forall w,
  RCycle d w ->
  exists w', TCycle d w'.
Proof.
  intros.
  assert (H':= C.cycle_b_to_cycle_a (GRG d) w H).
  tauto.
Qed.

End Dependencies.

Set Implicit Arguments.

Section Basic.
  Variable d:dependencies.
  Variable s:state.
  Variable d_of_s: Deps_of s d.

Let wedge_to_waits_for:
  forall r t,
  WEdge d t r ->
  WaitsFor s t r.
Proof.
  intros.
  unfold WEdge in H.
  assert (H':= d_of_s).
  destruct H' as (H', _).
  apply H' in H.
  assumption.
Qed.

Let waits_for_to_wedge:
  forall r t,
  WaitsFor s t r ->
  WEdge d t r.
Proof.
  intros.
  unfold WEdge in *.
  assert (H':= d_of_s).
  destruct H' as (H', _).
  apply H' in H.
  assumption.
Qed.

Lemma waits_for_eq_wedge:
  forall r t,
  WaitsFor s t r <-> WEdge d t r.
Proof.
  intros.
  split.
  apply waits_for_to_wedge.
  apply wedge_to_waits_for.
Qed.

Lemma iedge_eq_impedes:
  forall r t,
  IEdge d r t <-> Impedes s r t.
Proof.
  intros.
  split.
  - intros.
    unfold IEdge in *.
    assert (H':= d_of_s).
    destruct H' as (_, H').
    apply H'.
    auto.
  - intros.
    unfold IEdge.
    assert (H':= d_of_s).
    destruct H' as (_, H').
    apply H'.
    assumption.
Qed.

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