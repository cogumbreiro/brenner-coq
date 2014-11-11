Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetAVL.
Require Import Coq.Arith.Compare_dec.
Require Import
  Semantics TaskMap PhaserMap Vars Syntax.


Definition get_tasks (s:state) :taskmap := snd s.
Definition get_phasers (s:state) : phasermap := fst s.

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

Definition WaitsFor (r:resource) (w:waits) (t:tid) :=
  exists rs, Map_TID.MapsTo t rs w /\ Set_RES.In r rs.

Definition Impedes (t:tid) (I:impedes) (r:resource) :=
  exists ts, Map_RES.MapsTo r ts I /\ Set_TID.In t ts.

Definition le (r1:resource) (r2:resource) :=
  r1 = r2 \/ prec r1 r2.

Definition TEdge (e:t_edge) (d:dependencies) :=
  exists r1 r2,
  WaitsFor r1 (get_waits d) (fst e) /\
  Impedes (snd e) (get_impedes d) r2 /\
  le r1 r2.

Definition WFG_of (g:set_t_edge) (d:dependencies) :=
  forall e,
  Set_T.In e g <-> TEdge e d.

Definition REdge (e:r_edge) (d:dependencies) :=
  exists t,
  Impedes t (get_impedes d) (fst e) /\
  WaitsFor (snd e) (get_waits d) t.

Definition SG_of (g:set_r_edge) (d:dependencies) :=
  forall e,
  Set_R.In e g <-> REdge e d.

Inductive walk (A:Type) :=
  | Walk: A -> A -> walk A
  | WCons: A -> walk A -> walk A.

Definition head {A:Type} (w:walk A) : A :=
  match w with
    | Walk x _ => x
    | WCons x _ => x
  end.

Fixpoint tail {A:Type} (w:walk A) : A :=
  match w with
    | Walk _ x => x
    | WCons _ w' => tail w'
  end.

Inductive t_walk : walk tid -> dependencies -> Prop :=
  | TCons:
    forall x w d,
    t_walk w d ->
    TEdge (x, (head w)) d ->
    t_walk (WCons tid x w) d
  | TWalk:
    forall x y d,
    TEdge (x, y) d ->
    t_walk (Walk tid x y) d.

Inductive r_walk : walk resource -> dependencies -> Prop :=
  | RCons:
    forall x w d,
    r_walk w d ->
    REdge (x, (head w)) d ->
    r_walk (WCons resource x w) d
  | RWalk:
    forall x y d,
    REdge (x, y) d ->
    r_walk (Walk resource x y) d.

Inductive g_edge :=
  | g_edge_i: tid -> resource -> g_edge
  | g_edge_w: resource -> tid -> g_edge.

Definition THead (e:g_edge) (t:tid) :=
  match e with
    | g_edge_i t' _ => t = t'
    | _ => False
  end.

Definition RHead (e:g_edge) (r:resource) :=
  match e with
    | g_edge_w r' _ => r = r'
    | _ => False
  end.

Inductive g_walk : g_edge -> dependencies -> Prop  :=
  | GCons:
    forall x w d,
    g_walk w d ->
    REdge (x, (head w)) d ->
    r_walk (WCons resource x w) d
  | RWalk:
    forall x y d,
    REdge (x, y) d ->
    r_walk (Walk resource x y) d.


  | g_walk_i:
    forall r t d,
    Impedes t (get_impedes d) r ->
    g_walk (some_t t) (some_r r) d
  | g_walk_w:
    forall r t d,
    WaitsFor r (get_waits d) t ->
    g_walk (some_r r) (some_t t) d
  | g_cons_i:
    forall r t d,
    g_walk e1 e2 d ->
    
    Impedes t (get_impedes d) r ->
    g_walk (some_t t) (some_r r) d
  

