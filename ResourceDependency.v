Require Import
  Coq.Structures.OrderedTypeEx
  Coq.FSets.FSetAVL
  Coq.Arith.Compare_dec.

Require Import
  Semantics TaskMap PhaserMap Vars Syntax.

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
Module Map_RES := FMapAVL.Make RES.
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

Definition prec (r1:resource) (r2:resource) :=
  get_phaser r1 = get_phaser r2 /\ get_phase r1 < get_phase r2.

Section StateProps.

Variable s:state.

Definition Blocked (t:tid) (r:resource) :=
  exists prg,
  Map_TID.MapsTo t (pcons (Await (get_phaser r) (get_phase r)) prg) (get_tasks s) /\
  Map_PHID.In (get_phaser r) (get_phasers s).

Lemma blocked_fun:
  forall t r r',
  Blocked t r ->
  Blocked t r' ->
  r = r'.
Proof.
  intros.
  unfold Blocked in *.
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


Lemma mapsto_to_in : forall (elt:Type) m x (e:elt),
  Map_TID.MapsTo x e m -> Map_TID.In x m.
Proof.
  intros.
  rewrite Map_TID_Facts.find_mapsto_iff in H.
  assert (H1' : Map_TID.find (elt:=elt) x m <> None).
  - intuition.
    rewrite H in H0.
    inversion H0.
  - rewrite <- Map_TID_Facts.in_find_iff in H1'.
    assumption.
Qed.

Lemma opt_diff_none:
  forall {A:Type} (o:option A),
  o <> None ->
  exists v, o = Some v.
Proof.
  intros.
  destruct o.
  - exists a.
    auto.
  - contradiction H. auto.
Qed.

Lemma in_to_mapsto : forall (elt:Type) m x,
  Map_TID.In x m -> exists (e:elt), Map_TID.MapsTo x e m.
Proof.
  intros.
  rewrite Map_TID_Facts.in_find_iff in H.
  apply opt_diff_none in H.
  destruct H as (e, H).
  rewrite <- Map_TID_Facts.find_mapsto_iff in H.
  exists e. assumption.
Qed.

Lemma blocked_in_tasks:
  forall t r,
  Blocked t r ->
  Map_TID.In t (get_tasks s).
Proof.
  intros.
  unfold Blocked in H.
  destruct H as (p, (H1, H2)).
  apply mapsto_to_in in H1.
  assumption.
Qed.

Definition Registered (t:tid) (r:resource) :=
  exists ph,
  Map_PHID.MapsTo (get_phaser r) ph (get_phasers s) /\
  Map_TID.MapsTo t (get_phase r) ph /\ exists r', Blocked t r'.

Lemma registered_to_blocked:
  forall t r,
  Registered t r ->
  exists r', Blocked t r'.
Proof.
  intros.
  unfold Registered in H.
  destruct H as (ph, (H1, (H2, H3))).
  assumption.
Qed.

Definition W_of (w:waits) := 
  forall t r,
  (exists rs, Map_TID.MapsTo t rs w /\ Set_RES.In r rs)
  <->
  Blocked t r.

Definition I_of (i:impedes) :=
  forall t r,
  (exists ts, Map_RES.MapsTo r ts i /\ Set_TID.In t ts)
  <->
  (exists r',
  Registered t r' /\
  prec r' r /\ (exists r'', Blocked t r'')).

Definition Deps_of (d:dependencies) :=
  W_of (get_waits d) /\ I_of (get_impedes d).

End StateProps.

Definition TotallyDeadlocked (s:state) :=
  forall t r,
  (Map_TID.In t (get_tasks s) <-> Blocked s t r) /\
  Blocked s t r ->
  exists t',
  Map_TID.In t' (get_tasks s) /\
  (exists r', Registered s t' r' /\ prec r' r).
(*
  forall t,
  Map_TID.In t (get_tasks s) <->
  exists r, Blocked s t r /\ 
  exists t' r',
  Map_TID.In t' (get_tasks s) /\
  Registered s t' r' /\
  prec r' r.*)

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

Definition WaitsFor (d:dependencies) (r:resource) (t:tid) :=
  exists rs, Map_TID.MapsTo t rs (get_waits d) /\ Set_RES.In r rs.

Definition Impedes (d:dependencies) (t:tid) (r:resource) :=
  exists ts, Map_RES.MapsTo r ts (get_impedes d) /\ Set_TID.In t ts.


Definition GRG(d:dependencies) := B.mk_bipartite tid resource (Impedes d) (WaitsFor d).

Notation WFG d := (B.contract_a (GRG d)).
Notation SG d := (B.contract_b (GRG d)).
Notation TWalk d := (G.Walk (WFG d)).
Notation RWalk d := (G.Walk (SG d)).
Notation TCycle d := (G.Cycle (WFG d)).
Notation TEdge d := (G.Edge (WFG d)).
Notation RCycle d := (G.Cycle (SG d)).
Notation t_walk := (list t_edge).

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
