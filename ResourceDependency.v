Require Import
  Coq.Structures.OrderedTypeEx
  Coq.FSets.FSetAVL
  Coq.Arith.Compare_dec.

Require Import
  Semantics TaskMap PhaserMap Vars Syntax
  Graph.

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

Definition TEdge (e:t_edge) :=
  let (t1, t2) := e in
  exists r, WaitsFor r t1 /\ Impedes t2 r.

Lemma as_t_edge:
  forall r t1 t2,
  WaitsFor r t1 ->
  Impedes t2 r ->
  TEdge (t1, t2).
Proof.
  intros.
  unfold TEdge.
  exists r.
  auto.
Qed.

Definition WFG_of (g:set_t_edge) :=
  forall e, Set_T.In e g <-> TEdge e.

Definition REdge (e:r_edge) :=
  let (r1, r2) := e in
  exists t, Impedes t r1 /\ WaitsFor r2 t.

Lemma as_r_edge:
  forall t r1 r2,
  Impedes t r1 ->
  WaitsFor r2 t ->
  REdge (r1, r2).
Proof.
  intros.
  unfold REdge.
  exists t.
  auto.
Qed.

Definition SG_of (g:set_r_edge) :=
  forall e, Set_R.In e g <-> REdge e.

Notation TWalk := (Walk tid TEdge).
Notation TCycle := (Cycle tid TEdge).
Definition t_cycle_def := cycle_def tid TEdge.
Notation t_walk := (list t_edge).
Notation TEnd := (End tid).

Notation RWalk := (Walk resource REdge).
Notation RCycle := (Cycle resource REdge).
Definition r_cycle_def := cycle_def resource REdge.
Notation r_walk := (list r_edge).
Notation REnd := (End resource).

Notation g_edge := (g_vertex * g_vertex) % type.

Definition RTEdge (e:g_edge) :=
  let (x,y) := e in
  exists r t,
  IsResource x r /\
  IsTid y t /\
  Impedes t r.

Notation rt := (fun (r:resource) (t:tid) => ((GResource r), (GTid t))).
Notation RT := (fun (r:resource) (t:tid) => (RTEdge (rt r t))).

Lemma as_rt_edge:
  forall r t, 
  Impedes t r ->
  RT r t.
Proof.
  intros.
  unfold RTEdge.
  exists r.
  exists t.
  intuition.
  apply IsResource_def.
  apply IsTid_def.
Qed.

Definition TREdge (e:g_edge) :=
  let (x,y) := e in
  exists r t,
  IsTid x t /\
  IsResource y r /\
  WaitsFor r t.

Notation tr := (fun (t:tid) (r:resource) => ((GTid t), (GResource r))).
Notation TR := (fun (t:tid) (r:resource) => (TREdge (tr t r))).

Lemma as_tr_edge:
  forall t r,
  WaitsFor r t ->
  TR t r.
Proof.
  intros.
  unfold RTEdge.
  exists r.
  exists t.
  intuition.
  apply IsTid_def.
  apply IsResource_def.
Qed.

Definition GEdge (e:g_edge) :=
  TREdge e \/ RTEdge e.

Definition GWalk := Walk g_vertex GEdge.
Definition GCycle := Cycle g_vertex GEdge.

Lemma t_edge_to_g_edge:
  forall t1 t2,
  TEdge (t1, t2) ->
  exists r,
  TR t1 r /\ RT r t2.
Proof.
  intros.
  inversion H; clear H.
  destruct H0 as (H1, H2).
  simpl in *.
  exists x.
  intuition.
  apply_auto as_tr_edge.
  apply_auto as_rt_edge.
Qed.

Lemma g_edge_to_t_edge:
  forall t1 r t2,
  TR t1 r ->
  RT r t2 ->
  TEdge (t1, t2).
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
  apply as_t_edge with (r:= x0); r_auto.
Qed.

Lemma r_edge_to_g_edge:
  forall r1 r2,
  REdge (r1, r2) ->
  exists t,
  RT r1 t /\ TR t r2.
Proof.
  intros.
  inversion H; clear H.
  destruct H0 as (H1, H2).
  simpl in *.
  exists x.
  intuition.
  apply_auto as_rt_edge.
  apply_auto as_tr_edge.
Qed.

Lemma g_edge_to_r_edge:
  forall r1 t r2,
  RT r1 t ->
  TR t r2 ->
  REdge (r1, r2).
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
  apply as_r_edge with (t:=t1); r_auto.
Qed.

Definition RTR (r1:resource) (t:tid) (r2:resource) :=
  RT r1 t /\ TR t r2.

Definition TRT (t1:tid) (r:resource) (t2:tid) :=
  TR t1 r /\ RT r t2.

Lemma rtr_to_r:
  forall r1 t r2,
  RTR r1 t r2 ->
  REdge (r1, r2).
Proof.
  intros.
  destruct H.
  apply g_edge_to_r_edge with (t:=t); r_auto.
Qed.

Lemma r_to_rtr:
  forall r1 r2,
  REdge (r1, r2) ->
  exists t,
  RTR r1 t r2.
Proof.
  intros.
  unfold RTR.
  apply_auto r_edge_to_g_edge.
Qed.    

Lemma trt_to_t:
  forall t1 r t2,
  TRT t1 r t2 ->
  TEdge (t1, t2).
Proof.
  intros.
  destruct H.
  apply g_edge_to_t_edge with (r:=r); r_auto.
Qed.

Lemma t_to_trt:
  forall t1 t2,
  TEdge (t1, t2) ->
  exists r,
  TRT t1 r t2.
Proof.
  intros.
  unfold TRT.
  apply_auto t_edge_to_g_edge.
Qed.    

Lemma rtr_to_trt:
  forall r1 t1 r2 t2 r3,
  RTR r1 t1 r2 ->
  RTR r2 t2 r3 ->
  TRT t1 r2 t2.
Proof.
  intros.
  destruct H.
  destruct H0.
  unfold TRT.
  auto.
Qed.

Lemma trt_to_rtr:
  forall t1 r1 t2 r2 t3,
  TRT t1 r1 t2 ->
  TRT t2 r2 t3 ->
  RTR r1 t2 r2.
Proof.
  intros.
  destruct H.
  destruct H0.
  unfold RTR.
  auto.
Qed.

Lemma trt_to_r:
  forall t1 t2 t3 r1 r2,
  TRT t1 r1 t2 ->
  TRT t2 r2 t3 ->
  REdge (r1, r2).
Proof.
  intros.
  assert (H2: RTR r1 t2 r2).
  + apply trt_to_rtr with (t1:=t1) (t3:=t3); r_auto.
  + apply rtr_to_r with (t:=t2); r_auto.
Qed.

Lemma rtr_to_t:
  forall r1 r2 r3 t1 t2,
  RTR r1 t1 r2 ->
  RTR r2 t2 r3 ->
  TEdge (t1, t2).
Proof.
  intros.
  assert (H2: TRT t1 r2 t2).
  + apply rtr_to_trt with (r1:=r1) (r3:=r3); r_auto.
  + apply trt_to_t with (r:=r2); r_auto.
Qed.

Lemma trt_refl:
  forall t r,
  TRT t r t ->
  RTR r t r.
Proof.
  intros.
  assert (H1:= trt_to_rtr _ _ _ _ _ H H).
  assumption.
Qed.

Lemma rtr_refl:
  forall r t,
  RTR r t r ->
  TRT t r t.
Proof.
  intros.
  assert (H1:= rtr_to_trt _ _ _ _ _ H H).
  assumption.
Qed.

Inductive edge_t_to_r : t_edge -> t_edge -> r_edge -> Prop :=
  edge_t_to_r_def:
    forall t1 t2 t3 r1 r2,
    TRT t1 r1 t2 ->
    TRT t2 r2 t3 ->
    edge_t_to_r (t1, t2) (t2, t3) (r1, r2).

Lemma t_to_r_r_edge:
  forall e1 e2 e3,
  edge_t_to_r e1 e2 e3 ->
  REdge e3.
Proof.
  intros.
  inversion H.
  subst.
  assert (H2: RTR r1 t2 r2).
  apply trt_to_rtr with (t1:=t1) (t3:=t3); r_auto.
  apply rtr_to_r in H2; r_auto.
Qed.
 
Lemma edge_t_to_r_total:
  forall t1 t2 t3,
  TEdge (t1, t2) ->
  TEdge (t2, t3) ->
  exists r1 r2,
  edge_t_to_r (t1, t2) (t2, t3) (r1, r2).
Proof.
  intros.
  apply t_edge_to_g_edge in H.
  apply t_edge_to_g_edge in H0.
  destruct H as (r1, (H1, H2)).
  destruct H0 as (r2, (H3, H4)).
  exists r1.
  exists r2.
  intuition.
  apply edge_t_to_r_def.
  unfold TRT. auto.
  unfold TRT. auto.
Qed.

Inductive t_to_r : t_walk -> r_walk -> Prop :=
  | t_to_r_nil:
    t_to_r nil nil
  | t_to_r_edge_nil:
    forall e,
    t_to_r (e::nil) nil
  | t_to_r_cons:
    forall e1 e2 e tw rw,
    t_to_r (e2 :: tw) rw ->
    edge_t_to_r e1 e2 e ->
    t_to_r (e1 :: e2 :: tw)%list (e :: rw).

Lemma t_to_r_total_nil:
  exists rw : r_walk, t_to_r nil rw /\ RWalk rw.
Proof.
  exists nil.
  intuition.
  apply t_to_r_nil.
  apply walk_nil.
Qed.

Lemma t_to_r_total_edge:
  forall t1 t2,
  TWalk ((t1, t2) :: nil) ->
  exists rw : r_walk, t_to_r ((t1, t2) :: nil) rw /\ RWalk rw.
Proof.
  exists nil.
  intuition.
  apply t_to_r_edge_nil.
  apply walk_nil.  
Qed.

Lemma t_walk_to_t_to_r_edge:
  forall t1 t2 t3 tw,
  TWalk ((t1, t2) :: ((t2, t3) :: tw)%list) ->
  exists r1 r2, edge_t_to_r (t1, t2) (t2, t3) (r1, r2).
Proof.
  intros.
  inversion H; subst.
  inversion H2; subst.
  apply_auto edge_t_to_r_total.
Qed.

Lemma edge_t_to_r_inv1:
  forall t1 t2 t3 r1 r2,
  edge_t_to_r (t1, t2) (t2, t3) (r1, r2) ->
  TRT t1 r1 t2.
Proof.
  intros. inversion H.
  assumption.
Qed.

Lemma edge_t_to_r_inv2:
  forall t1 t2 t3 r1 r2,
  edge_t_to_r (t1, t2) (t2, t3) (r1, r2) ->
  TRT t2 r2 t3.
Proof.
  intros. inversion H.
  assumption.
Qed.

Lemma edge_t_to_r_inv3:
  forall t1 t2 t3 r1 r2,
  edge_t_to_r (t1, t2) (t2, t3) (r1, r2) ->
  RTR r1 t2 r2.
Proof.
  intros. inversion H.
  apply trt_to_rtr with (t1:=t1) (t3:=t3); r_auto.
Qed.

Lemma r_walk_cons_trt:
  forall r0 r1 r2 t1 t2 t3 rw,
  TRT t1 r0 t2 ->
  TRT t2 r1 t3 ->
  RWalk ((r1, r2) :: rw) ->
  RWalk ((r0, r1) :: ((r1, r2) :: rw)%list).
Proof.
  intros.
  inversion H0; subst.
  apply walk_cons.
  - assumption.
  - apply trt_to_r with (t1:=t1) (t2:=t2) (t3:=t3); r_auto.
  - compute; auto.
Qed.

Lemma t_to_r_cons_trt:
  forall t1 t2 t3 t4 tw r0 r1 r2 rw,
  TRT t1 r0 t2 ->
  TRT t2 r1 t3 ->
  t_to_r ((t2, t3) :: ((t3, t4) :: tw)%list) ((r1, r2) :: rw)
  ->
  t_to_r ((t1, t2) :: ((t2, t3) :: (t3, t4) :: tw)%list)
  ((r0, r1) :: ((r1, r2) :: rw)%list).
Proof.
  intros.
  assert (H5': edge_t_to_r (t1, t2) (t2, t3) (r0, r1)).
  * apply_auto edge_t_to_r_def.
  * apply_auto t_to_r_cons.
Qed.

Lemma t_to_r_r_walk_cons:
  forall t1 t2 t3 t4 tw r0 r1 r2 rw,
  TRT t1 r0 t2 ->
  TRT t2 r1 t3 ->
  RWalk ((r1, r2) :: rw) ->
  edge_t_to_r (t2, t3) (t3, t4) (r1, r2) ->
  t_to_r ((t2, t3) :: ((t3, t4) :: tw))%list ((r1, r2) :: rw)
  ->
  t_to_r ((t1, t2) :: ((t2, t3) :: (t3, t4) :: tw)%list)
  ((r0, r1) :: ((r1, r2) :: rw)%list)
  /\
  RWalk ((r0, r1) :: ((r1, r2) :: rw)%list).
Proof.
  intuition.
  + apply_auto t_to_r_cons_trt.
  + apply edge_t_to_r_inv1 in H2.
    apply r_walk_cons_trt with (t1:=t1) (t2:=t2) (t3:=t3); r_auto.
Qed.

Lemma edge_t_to_r_to_r_walk:
  forall t1 t2 t3 r1 r2,
  edge_t_to_r (t1, t2) (t2, t3) (r1, r2) ->
  RWalk ((r1, r2) :: nil).
Proof.
  intros.
  apply walk_cons.
  * apply walk_nil.
  * apply t_to_r_r_edge in H.
    assumption.
  * compute;
    auto.
Qed.

Lemma t_to_r_total_step:
  forall t1 t2 t3 tw rw,
  TWalk ((t1, t2) :: ((t2, t3) :: tw)%list) ->
  t_to_r ((t2, t3) :: tw) rw ->
  RWalk rw ->
  exists rw' : r_walk,
  t_to_r ((t1, t2) :: ((t2, t3) :: tw)%list) rw' /\ RWalk rw'.
Proof.
  intros.
  assert (H3: TEdge (t1, t2)).
  inversion H; subst; assumption.
  inversion H0.
  - (* Case 1: *)
    subst.
    assert (Hr := H).
    apply t_walk_to_t_to_r_edge in Hr.
    destruct Hr as (r1, (r2, Hr)).
    exists (cons (r1, r2) nil).
    intuition.
    + apply_auto t_to_r_cons.
    + apply edge_t_to_r_to_r_walk with (t1:=t1) (t2:=t2) (t3:=t3); r_auto.
  - (* Case 2: *)
    subst.
    destruct e2 as (t3', t4).
    inversion H7; subst. (* t3 = t3' *)
    apply t_to_trt in H3; destruct H3 as (r0, H3).
    exists ((r0, r1) :: (r1, r2):: rw0)%list.
    apply_auto t_to_r_r_walk_cons.
Qed.

Lemma t_to_r_total:
  forall tw,
  TWalk tw ->
  exists tr, t_to_r tw tr /\ RWalk tr.
Proof.
  intros.
  induction tw.
  - apply t_to_r_total_nil.
  - inversion H.
    subst.
    apply IHtw in H2; clear IHtw.
    destruct H2 as (tr, (H1, H2)).
    destruct a as (t1, t2).
    destruct tw.
    + apply_auto t_to_r_total_edge.
    + destruct p as (t2', t3).
      (* t2 = t2' *)
      compute in H4; rewrite <- H4 in *; clear H4.
      apply t_to_r_total_step with (rw := tr); r_auto.
Qed.

Lemma t_to_r_step:
  forall tw r1 r2 tr,
  TWalk tw ->
  t_to_r tw ((r1,r2)::tr) ->
  RWalk ((r1,r2)::tr) ->
  exists t1 t2 t3 tw',
  (tw = ((t1,t2)::(t2,t3)::tw')%list /\ 
  TRT t1 r1 t2 /\ TRT t2 r2 t3).
Proof.
  intros.
  inversion H0.
  - subst.
    destruct e1 as (t1,t2).
    destruct e2 as (t2',t3).
    exists t1;
    exists t2;
    exists t3;
    exists tw0.
    intuition.
    + inversion H.
      compute in H8.
      subst.
      auto.
    + inversion H6.
      auto.
    + inversion H6.
      auto.
Qed.

Inductive TComplement : t_walk -> r_walk -> Prop :=
  t_complement_def:
    forall tw rw,
    TWalk tw ->
    RWalk rw ->
    t_to_r tw rw ->
    TComplement tw rw.

Lemma t_complement_decons:
  forall tw rw e1 e2,
  TComplement (e1::tw) (e2::rw) ->
  TComplement tw rw.
Proof.
  intros.
  inversion H; subst; clear H.
  inversion H0; inversion H1; inversion H2; clear H0 H1 H2; subst.
  apply_auto t_complement_def.
Qed.

Lemma tcomplement_to_end:
  forall e1 e2 tw rw e e',
  TComplement (e1::tw) (e2::rw) ->
  TEnd (e1::tw) e ->
  REnd (e2::rw) e' ->
  exists e'',
  TComplement (e''::e::nil)%list (e'::nil).
Proof.
  intros.
  induction tw.

Lemma r_walk_end:
  forall t t' tw rw,
  TWalk tw ->
  t_to_r tw rw ->
  RWalk rw ->
  End tid tw (t, t') ->
  rw <> nil ->
  exists r r',
  (TRT t r t' /\ End resource rw (r', r)).
Proof.
  intros.
  inversion H0; subst; inversion H2.
   - intuition. (* absurd *)
   - intuition. (* absurd *)
   - subst.
     destruct e as (r1, r2).
     assert (H6:=end_total resource (r1,r2) rw0 ).
     destruct H6 as (e, Hend).
     destruct e as (r', r);
     exists r'; exists r.
     intuition.
     
Qed.    

Lemma wfg_to_sg:
  forall w,
  TCycle w ->
  exists w', RCycle w'.
Proof.
  intros.
  inversion H; clear H; subst.
  inversion H1; subst.
  apply t_to_r_total in H3.
  destruct H3 as (tr, (H2, H3)).
  inversion H2.
  - subst.
    apply end_inv in H0. inversion H0. subst.
    apply t_to_trt in H4.
    destruct H4 as (r, H4).
    apply trt_refl in H4.
    apply rtr_to_r in H4.
    exists ((r,r) :: nil)%list.
    assert (Hs : End resource ((r,r)::nil) (r,r)). apply end_nil.
    assert (Hw : RWalk ((r,r)::nil)).
      apply walk_cons. apply walk_nil. assumption. compute. reflexivity.
    apply r_cycle_def with (vn:=r).
    assumption.
    assumption.
  - subst.
    inversion H0; clear H0; subst.
    assert (Hr := H8). 
    apply end_inv in H8; inversion H8; subst; clear H. (* e = (vn, v1) *)
    inversion H5; compute in H; subst; clear H5. (* v2 = vn *)
    inversion H1; subst; inversion H5; subst.
    apply t_to_trt in H6.
    apply t_to_trt in H9.
    destruct H6 as (r1, H6).
    destruct H9 as (r2, H9).
    assert (Hr1 : RTR r1 vn r2).
    apply trt_to_rtr with (t1 := v1) (t3:=v1).
      assumption. assumption.
    assert (Hr2 : RTR r2 v1 r1).
      apply trt_to_rtr with (t1 := vn) (t3:=vn).
      assumption. assumption.
    apply rtr_to_r in Hr1.
    apply rtr_to_r in Hr2.
    exists ((r1,r2)::(r2, r1)::nil)%list.
    apply r_cycle_def with (vn:=r2).
    + apply end_cons.
      apply end_nil.
    + apply walk_cons.
      apply walk_cons.
      apply walk_nil.
      assumption.
      compute. reflexivity.
      assumption.
      compute; reflexivity.
  - subst.
    destruct e1 as (t1, t2).
    destruct e2 as (t2', t3).
    destruct e as (r1, r2).
    inversion H6; subst. (* t2 = t2' *)
    compute in H5; subst. (* v2 = t2 *)
    assert (H5 : exists r1', TRT vn r1' v1).
      assert (H5 : TEdge (vn, v1)).
        apply start_to_edge with (w:=(cons (v1, t1) ((t1, t2') :: (t2', t3) :: tw)%list)).
        assumption.
        assumption.
      apply t_to_trt.
      assumption.
    destruct H5 as (rn, H5).
    inversion H1; subst.
    apply t_to_trt in H11.
    destruct H11 as (r0, H11); clear H12.
    assert (H7 : RTR r0 t1 r1).
      apply trt_to_rtr with (t1:=v1) (t3:=t2').
      assumption.
      assumption.
    
Qed.
End Dependencies.
