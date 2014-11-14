Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetAVL.
Require Import Coq.Arith.Compare_dec.
Require Import
  Semantics TaskMap PhaserMap Vars Syntax.

Definition get_tasks (s:state) :taskmap := snd s.
Definition get_phasers (s:state) : phasermap := fst s.

Section Walk.
Variable Implicit A:Type.
Notation edge := (A*A)%type.
Variable Edge : edge -> Prop.
Notation walk := (list edge).

Definition head (e:edge) : A := fst e.
Definition tail (e:edge) : A := snd e.
Definition walk_head (default:A) (w:walk) : A := head (List.hd (default, default) w).

Definition Linked e w := tail e = walk_head (tail e) w.

Inductive Walk : walk -> Prop :=
  | WCons:
    forall e w,
    Walk w ->
    Edge e ->
    Linked e w ->
    Walk (e :: w)
  | WNil:
    Walk nil.

Lemma in_edge:
  forall e w,
  Walk w ->
  List.In e w ->
  Edge e.
Proof.
  intros.
  induction w.
  inversion H0.
  apply List.in_inv in H0.
  destruct H0.
  subst.
  inversion H.
  assumption.
  inversion H.
  subst.
  apply IHw in H3.
  assumption.
  assumption.
Qed.

Inductive VertexIn : A -> walk -> Prop :=
  | VertexIn_head:
    forall e w,
    List.In e w ->
    VertexIn (head e) w
  | VertexIn_tail:
    forall e w,
    List.In e w ->
    VertexIn (tail e) w.

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
Notation t_walk := (list t_edge).

Notation RWalk := (Walk resource REdge).
Notation r_walk := (list r_edge).

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
  apply as_tr_edge; assumption.
  apply as_rt_edge; assumption.
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
  apply as_t_edge with (r:= x0).
  assumption.
  assumption.
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
  apply as_rt_edge.
  assumption.
  apply as_tr_edge.
  assumption.
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
  apply as_r_edge with (t:=t1).
  assumption.
  assumption.
Qed.

Inductive edge_t_to_r : t_edge -> t_edge -> r_edge -> Prop :=
  edge_t_to_r_def:
    forall t1 t2 t3 r1 r2,
    TR t1 r1 ->
    RT r1 t2 ->
    TR t2 r2 ->
    RT r2 t3 ->
    edge_t_to_r (t1, t2) (t2, t3) (r1, r2).

Lemma t_to_r_r_edge:
  forall e1 e2 e3,
  edge_t_to_r e1 e2 e3 ->
  REdge e3.
Proof.
  intros.
  inversion H.
  subst.
  apply g_edge_to_r_edge with (t:=t2).
  assumption.
  assumption.
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
  assumption.
  assumption.
  assumption.
  assumption.
Qed.

Inductive t_to_r : t_walk -> r_walk -> Prop :=
  | t_to_r_nil_nil:
    t_to_r nil nil
  | t_to_r_nil_edge:
    forall e,
    t_to_r (e::nil) nil
  | t_to_r_cons:
    forall e1 e2 e tw rw,
    t_to_r (e2 :: tw) rw ->
    edge_t_to_r e1 e2 e ->
    (*Linked resource e rw ->*)
    t_to_r (e1 :: e2 :: tw)%list (e :: rw).

Lemma t_to_r_total:
  forall tw,
  TWalk tw ->
  exists tr, t_to_r tw tr.
Proof.
  intros.
  induction tw.
  - exists nil.
    intuition.
    apply t_to_r_nil_nil.
  - inversion H.
    subst.
    apply IHtw in H2; clear IHtw.
    destruct H2 as (tr, H1).
    destruct tw.
    + inversion H1.
      subst.
      exists nil.
      intuition.
      apply t_to_r_nil_edge.
    + inversion H; subst.
      inversion H5; subst.
      destruct a as (t1, t2).
      destruct p as (t2', t3).
      compute in H7.
      rewrite <- H7 in *; clear H7.
      assert (Hr := edge_t_to_r_total _ _ _ H3 H9).
      destruct Hr as (r1, (r2, Hr)).
      exists (cons (r1, r2) tr).
      apply t_to_r_cons.
      assumption.
      assumption.
Qed.

Lemma t_to_r_walk:
  forall tw tr,
  TWalk tw ->
  t_to_r tw tr ->
  RWalk tr.
Proof.
  induction tw.
  - intros.
    inversion H0.
    apply WNil.
  - intros.
    inversion H0.
    + subst.
      apply WNil.
    + subst.
      inversion H.
      subst.
      apply (IHtw rw) in H4; clear IHtw.
      destruct a as (t1, t2).
      inversion H5; clear H5; subst.
      apply WCons.
      assumption.
      apply g_edge_to_r_edge with (t:=t2).
      assumption.
      assumption.
      assumption.
    
Qed.
Definition TComplement (tw:t_walk) (rw:r_walk) :=
  (forall r, VertexIn resource r rw ->
    exists (t1 t2:tid), List.In (t1, t2) tw /\ TR t1 r /\ RT r t2).

(*
Lemma t_complement_cons:
  forall e tw rw,
  TWalk (e :: tw) ->
  RWalk rw ->
  TComplement tw rw ->
  exists e', TComplement (e :: tw) (e' :: rw).
Proof.
  intros.
  unfold TComplement in *.
  inversion H.
  subst.
  destruct e as (t1, t2).
  simpl in H6.
  apply t_edge_to_g_edge in H5.
  destruct H5 as (r, (H2, H3)).
  destruct tw.
  - assert (H1' := H1 r); clear H1.
Qed.
  *)
  
Lemma t_walk_to_r_walk:
  forall tw,
  TWalk tw ->
  exists rw, RWalk rw /\ TComplement tw rw.
Proof.
  intros.
  induction tw.
  - exists nil.
    intros.
    intuition.
    apply WNil.
    unfold TComplement.
    intros.
    inversion H0.
    inversion H1.
    inversion H1.
  - inversion H.
    subst.
    apply IHtw in H2; clear IHtw.
    destruct H2 as (rw, (H2, H5)).
Qed.
    
End Dependencies.
