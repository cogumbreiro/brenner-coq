Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetAVL.
Require Import Coq.Arith.Compare_dec.
Require Import
  Semantics TaskMap PhaserMap Vars Syntax.

Definition get_tasks (s:state) :taskmap := snd s.
Definition get_phasers (s:state) : phasermap := fst s.

Section Walk.
Variable Implicit A:Type.
Variable Edge : A -> A -> Prop.

Inductive Head: A -> list A -> Prop :=
  Head_def:
    forall h l,
    Head h (h :: l).

Inductive walk : list A -> Prop :=
  | WCons:
    forall x y w,
    walk w ->
    Head y w ->
    Edge x y ->
    walk (cons x w)
  | WNil:
    forall x y,
    Edge x y ->
    walk (cons x (cons y nil)).

Inductive In: (A*A) -> list A -> Prop :=
  | In_ok:
    forall x y w,
    In (x, y) (cons x (cons y w))
  | In_cons:
    forall p x w,
    In p w ->
    In p (cons x w).

Lemma walk_to_edge:
  forall t1 t2 w,
  walk (cons t1 (cons t2 w)) ->
  Edge t1 t2 /\ (w <> nil -> walk (cons t2 w)).
Proof.
  intros.
  inversion H.
  - subst.
    inversion H3.
    subst.
    intuition.
  - intuition.
Qed.

Lemma edge_to_walk:
  forall t1 t2 w,
  Edge t1 t2 ->
  walk (cons t2 w) ->
  walk (cons t1 (cons t2 w)).
Proof.
  intros.
  apply WCons with (y := t2).
  assumption.
  apply Head_def.
  assumption.
Qed.
End Walk.

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

Definition Blocked (t:tid) (r:resource) (s:state) :=
  exists prg,
  Map_TID.MapsTo t (pcons (Await (get_phaser r) (get_phase r)) prg) (get_tasks s) /\
  Map_PHID.In (get_phaser r) (get_phasers s).

Definition Registered (t:tid) (r:resource) (s:state) :=
  exists ph,
  Map_PHID.MapsTo (get_phaser r) ph (get_phasers s) /\
  Map_TID.MapsTo t (get_phase r) ph.

Definition TotallyDeadlocked (s:state) :=
  forall t,
  Map_TID.In t (get_tasks s) /\
  exists r,
  Blocked t r s /\ 
  exists t',
  Map_TID.In t' (get_tasks s) /\
  exists r',
  Registered t' r' s /\
  prec r' r.

Definition Deadlocked (s:state) :=
  exists tm tm',
  Map_TID_Props.Disjoint tm tm' /\
  Map_TID.Equal (get_tasks s) (Map_TID_Props.update tm tm') /\
  TotallyDeadlocked ((get_phasers s), tm).

Definition W_of (w:waits) (s:state) := 
  forall t r,
  (exists rs, Map_TID.MapsTo t rs w /\ Set_RES.In r rs)
  <->
  Blocked t r s.

Definition I_of (i:impedes) (s:state) :=
  forall t r,
  (exists ts, Map_RES.MapsTo r ts i /\ Set_TID.In t ts)
  <->
  (exists t' r',
  Registered t' r s /\
  Blocked t r' s /\
  prec r' r).

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

Inductive g_vertex :=
  | GResource : resource -> g_vertex
  | GTid : tid -> g_vertex.

Inductive IsResource: g_vertex -> resource -> Prop :=
  IsResource_def : forall r, IsResource (GResource r) r.

Lemma IsResource_inv:
  forall x y,
  IsResource (GResource x) y ->
  x = y.
Proof.
  intros.
  inversion H.
  reflexivity.
Qed.

Inductive IsTid: g_vertex -> tid -> Prop :=
  IsTid_def : forall t, IsTid (GTid t) t.

Lemma IsTid_inv:
  forall x y,
  IsTid (GTid x) y ->
  x = y.
Proof.
  intros.
  inversion H.
  reflexivity.
Qed.

Section Dependencies.

Variable d:dependencies.

Definition WaitsFor (r:resource) (t:tid) :=
  exists rs, Map_TID.MapsTo t rs (get_waits d) /\ Set_RES.In r rs.

Definition Impedes (t:tid) (r:resource) :=
  exists ts, Map_RES.MapsTo r ts (get_impedes d) /\ Set_TID.In t ts.

Definition TEdge (t1:tid) (t2:tid) :=
  exists r, WaitsFor r t1 /\ Impedes t2 r.

Definition WFG_of (g:set_t_edge) :=
  forall e, Set_T.In e g <-> TEdge (fst e) (snd e).

Definition REdge (r1:resource) (r2:resource) :=
  exists t, Impedes t r1 /\ WaitsFor r2 t.

Definition SG_of (g:set_r_edge) :=
  forall e, Set_R.In e g <-> REdge (fst e) (snd e).

Definition t_walk := walk tid TEdge.

Definition r_walk := walk resource REdge.

Definition RTEdge (x:g_vertex) (y:g_vertex) :=
  exists r t,
  IsResource x r /\
  IsTid y t /\
  Impedes t r.

Definition TREdge (x:g_vertex) (y:g_vertex) :=
  exists r t,
  IsTid x t /\
  IsResource y r /\
  WaitsFor r t.

Definition GEdge (x:g_vertex) (y:g_vertex) :=
  TREdge x y \/ RTEdge x y.

Definition g_walk := walk g_vertex GEdge.

Lemma t_walk_to_edge:
  forall t1 t2 w,
  t_walk (cons t1 (cons t2 w)) ->
  TEdge t1 t2 /\ (w <> nil -> t_walk (cons t2 w)).
Proof.
  intros.
  inversion H.
  - subst.
    inversion H3.
    subst.
    intuition.
  - intuition.
Qed.

Lemma t_edge_to_walk:
  forall t1 t2 w,
  TEdge t1 t2 ->
  t_walk (cons t2 w) ->
  t_walk (cons t1 (cons t2 w)).
Proof.
  intros.
  apply WCons with (y := t2).
  assumption.
  apply Head_def.
  assumption.
Qed.

Lemma t_edge_to_g_edge:
  forall t1 t2,
  TEdge t1 t2 ->
  exists r,
  TREdge (GTid t1) (GResource r) /\ RTEdge (GResource r) (GTid t2).
Proof.
  intros.
  inversion H; clear H.
  destruct H0 as (H1, H2).
  simpl in *.
  exists x.
  intuition.
  unfold TREdge.
  exists x.
  exists t1.
  intuition.
  apply IsTid_def.
  apply IsResource_def.
  unfold RTEdge.
  exists x.
  exists t2.
  intuition.
  apply IsResource_def.
  apply IsTid_def.
Qed.

Lemma g_edge_to_t_edge:
  forall t1 r t2,
  TREdge (GTid t1) (GResource r) ->
  RTEdge (GResource r) (GTid t2) ->
  TEdge t1 t2.
Proof.
  intros.
  inversion H; clear H.
  destruct H1 as (t, (H3,(H4,H5))).
  apply IsTid_inv in H3.
  apply IsResource_inv in H4.
  subst.
  inversion H0; clear H0.
  destruct H as (t1, (H1,(H2,H3))).
  apply IsTid_inv in H2.
  apply IsResource_inv in H1.
  subst.
  unfold TEdge.
  exists x0.
  auto.
Qed.

Lemma r_edge_to_g_edge:
  forall r1 r2,
  REdge r1 r2 ->
  exists t,
  RTEdge (GResource r1) (GTid t) /\ TREdge (GTid t) (GResource r2).
Proof.
  intros.
  inversion H; clear H.
  destruct H0 as (H1, H2).
  simpl in *.
  exists x.
  intuition.
  unfold RTEdge.
  exists r1.
  exists x.
  intuition.
  apply IsResource_def.
  apply IsTid_def.
  unfold TREdge.
  exists r2.
  exists x.
  intuition.
  apply IsTid_def.
  apply IsResource_def.
Qed.

Lemma g_edge_to_r_edge:
  forall r1 t r2,
  RTEdge (GResource r1) (GTid t) ->
  TREdge (GTid t) (GResource r2) ->
  REdge r1 r2.
Proof.
  intros.
  inversion H; clear H.
  destruct H1 as (t', (H3,(H4,H5))).
  apply IsTid_inv in H4.
  apply IsResource_inv in H3.
  subst.
  inversion H0; clear H0.
  destruct H as (t1, (H1,(H2,H3))).
  apply IsTid_inv in H1.
  apply IsResource_inv in H2.
  subst.
  unfold REdge.
  exists t1.
  auto.
Qed.

Lemma t_walk_to_r_walk:
  forall t t' t'' tw,
  t_walk (cons t (cons t' (cons t'' tw))) ->
  exists rw,
  r_walk rw ->
  forall r,
  List.In r rw ->
  exists (t1 t2:tid),
  In tid (t1, t2) tw /\
  TREdge (GTid t1) (GResource r) /\
  RTEdge (GResource r) (GTid t2).
Proof.
  intros.
  induction tw.
  - inversion H; clear H.
    subst.
    inversion H3; clear H3.
    subst.
    inversion H2; clear H2.
    subst.
    inversion H3; clear H3.
    subst.
    clear H1.
    inversion H4; clear H4.
    inversion H5; clear H5.
    destruct H as (H1, H2).
    destruct H0 as (H3, H4).
    exists (cons x (cons x0 nil)).
  - subst.
    apply IHtw in H2; clear IHtw.
    destruct H2 as (rw, H2).
    exists rw.
    intros.
    destruct (H2 H _ H0) as (t1, (t2, (H1, (H5, H6)))); clear H H0 H2.
    exists t1; exists t2.
    apply In_cons with (x := a) in H1.
    auto.
  - subst.
    clear IHtw. (* cannot be used *)
    
End Dependencies.
