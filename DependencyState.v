Require Import Vars.
Require Import ResourceDependency.
Require Import Semantics.

Set Implicit Arguments.

(** The type of map I ranges from resources to sets of tasks. *)
Definition impedes := Map_RES.t set_tid.

(** The type of map W ranges tasks to sets of resources. *)
Definition waits := Map_TID.t set_resource.

(** A dependency state *)
Definition dependencies := (impedes * waits) % type.
Definition get_waits (d:dependencies) : waits := snd d.
Definition get_impedes (d:dependencies) : impedes := fst d.

(** A w-edge is an edge in the dependency state such that `r in W(t)`. *)
Definition WDep (w:waits) (t:tid) (r:resource) :=
  exists rs, Map_TID.MapsTo t rs w /\ Set_RES.In r rs.

(** We build the phaser map of waiting tasks to be constituted by all
   blocked tasks in state [s]. *)
Definition W_of (s:state) (w:waits) := forall t r, WDep w t r <-> WaitsFor s t r.

(** A resource [r] impedes a task [r] if task [t] is registered in a
   preceeding resource; the impeding resource must be the target of
   a blocked task. *)

(* An i-edge is an edge in the dependency state such that `t in I(t)`. *)
Definition IDep (i:impedes) (r:resource) (t:tid) :=
  exists ts, Map_RES.MapsTo r ts i /\ Set_TID.In t ts.

(** The map of impedes holds all resources that are blocking a task. *)
Definition I_of (s:state) (i:impedes) := forall t r, IDep i r t <-> Impedes s r t.

Definition Deps_of (s:state) (d:dependencies) := W_of s (get_waits d) /\ I_of s (get_impedes d).

Notation WEdge d := (WDep (get_waits d)).
Notation IEdge d := (IDep (get_impedes d)).

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
  unfold WDep in H.
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
  unfold WDep in *.
  assert (H':= d_of_s).
  destruct H' as (H', _).
  apply H' in H.
  assumption.
Qed.

(** If we have that [d] are the state-depencies of
    a state [s], then a W-edge is equivalent to a waits-for
    relation. *)
Lemma wedge_eq_waits_for:
  forall r t,
  WEdge d t r <-> WaitsFor s t r.
Proof.
  intros.
  split.
  apply wedge_to_waits_for.
  apply waits_for_to_wedge.
Qed.

(** Similarly, an i-edge is equivalent to an impedes relation. *)
Lemma iedge_eq_impedes:
  forall r t,
  IEdge d r t <-> Impedes s r t.
Proof.
  intros.
  split.
  - intros.
    unfold IDep in *.
    assert (H':= d_of_s).
    destruct H' as (_, H').
    apply H'.
    auto.
  - intros.
    unfold IDep.
    assert (H':= d_of_s).
    destruct H' as (_, H').
    apply H'.
    assumption.
Qed.

End Basic.