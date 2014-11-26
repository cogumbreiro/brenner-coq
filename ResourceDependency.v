Require Import
  Coq.Structures.OrderedTypeEx
  Coq.FSets.FSetAVL
  Coq.Arith.Compare_dec.

Require Import
  Semantics TaskMap PhaserMap Vars Syntax
  Graph Bipartite.

Require OBipartite.
Require OGraph.

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


Lemma mapsto_to_in : forall (elt:Type) m x (e e':elt),
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
  auto.
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

Section Dependencies.

Variable d:dependencies.

Definition WaitsFor (r:resource) (t:tid) :=
  exists rs, Map_TID.MapsTo t rs (get_waits d) /\ Set_RES.In r rs.

Definition Impedes (t:tid) (r:resource) :=
  exists ts, Map_RES.MapsTo r ts (get_impedes d) /\ Set_TID.In t ts.


Definition GRG := OBipartite.mk_bipartite tid resource Impedes WaitsFor.
Definition WFG := OBipartite.contract_a GRG.
Definition SG := OBipartite.contract_b GRG.
Definition TWalk := OGraph.Walk WFG.
Definition RWalk := OGraph.Walk SG.
Definition TCycle := OGraph.Cycle WFG.
Definition RCycle := OGraph.Cycle SG.
Definition t_walk := OGraph.walk WFG.

Theorem wfg_to_sg:
  forall w,
  TCycle w ->
  exists w', RCycle w'.
Proof.
  intros.
  assert (H':= OBipartite.cycle_a_to_cycle_b GRG w H).
  tauto.
Qed.

Theorem sg_to_wfg:
  forall w,
  RCycle w ->
  exists w', TCycle w'.
Proof.
  intros.
  assert (H':= OBipartite.cycle_b_to_cycle_a GRG w H).
  tauto.
Qed.

End Dependencies.

Section Correctness.
  Variable d:dependencies.
  Variable s:state.
  Parameter d_of_s: Deps_of s d.

Lemma waits_for_to_blocked:
  forall r t,
  WaitsFor d r t ->
  Blocked s t r.
Proof.
  intros.
  unfold WaitsFor in H.
  assert (H':= d_of_s).
  destruct H' as (H', _).
  apply H' in H.
  assumption.
Qed.

Lemma blocked_to_waits_for:
  forall r t,
  Blocked s t r ->
  WaitsFor d r t .
Proof.
  intros.
  unfold WaitsFor in *.
  assert (H':= d_of_s).
  destruct H' as (H', _).
  apply H' in H.
  assumption.
Qed.

Lemma blocked_eq_waits_for:
  forall r t,
  Blocked s t r <->
  WaitsFor d r t .
Proof.
  intros.
  split.
  apply blocked_to_waits_for.
  apply waits_for_to_blocked.
Qed.

Lemma impedes_to_registered:
  forall t r,
  Impedes d t r ->
  exists r', Registered s t r' /\ prec r' r.
Proof.
  intros.
  unfold Impedes in H.
  assert (H':= d_of_s).
  destruct H' as (_, H').
  apply H' in H.
  destruct H as (r', H).
  exists r'.
  intuition.
Qed.

Lemma registered_to_impedes :
  forall t r' r,
  Registered s t r' ->
  prec r' r ->
  Impedes d t r.
Proof.
  intros.
  unfold Impedes.
  assert (H':= d_of_s).
  destruct H' as (_, H').
  apply H'.
  exists r'.
  intuition.
  inversion H.
  destruct H1 as (_, (_, H1)).
  assumption.
Qed.
  
Lemma impedes_eq_registered:
  forall t r,
  Impedes d t r <->
  exists r', Registered s t r' /\ prec r' r.
Proof.
  intros.
  intuition.
  - apply_auto impedes_to_registered.
  - destruct H as (r', (H1, H2)).
    apply registered_to_impedes with (r':=r'); r_auto.
Qed.

Lemma tedge_inv:
  forall w t t',
  TWalk d w ->
  List.In (t, t') w ->
  exists r,
  Impedes d t r /\ WaitsFor d r t'.
Proof.
  intros.
  apply in_edge with (Edge:=OGraph.Edge (WFG d)) in H0.
  simpl in H0.
  inversion H0.
  simpl in *.
  subst.
  exists b.
  intuition.
  assumption.
Qed.

Section TotallyDeadlockedSoundness.
Variable w:t_walk d.

Variable is_cycle: TCycle d w.

Variable all_in_walk:
  forall t,
  Map_TID.In t (get_waits d) ->
  exists t', List.In (t', t) w \/ List.In (t, t') w.

Let Hwalk: TWalk d w.
Proof.
  intros.
  inversion is_cycle.
  assumption.
Qed.

Lemma in_waits_to_edge : 
  forall t,
  Map_TID.In t (get_waits d) ->
  exists t', List.In (t', t) w.
Proof.
  intros.
  apply all_in_walk in H.
  destruct H as (t', [H|H]).
  - exists t'. assumption.
  - apply pred_in_cycle with (Edge:=OGraph.Edge (WFG d)) in H.
    destruct H as (t'', H).
    exists t''.
    + assumption.
    + assumption.
Qed.

Lemma blocked_in_waits:
  forall t r,
  Blocked s t r ->
  Map_TID.In t (get_waits d).
Proof.
  intros.
  destruct d_of_s as (Hw, Hi).
  unfold W_of in Hw.
  assert (H':= Hw t r).
  rewrite <- H' in H.
  destruct H as (rs, (H1, H2)).
  apply mapsto_to_in with (e:=rs); r_auto.
Qed.

Lemma in_inv_left:
  forall t t',
  List.In (t, t') w ->
  Map_TID.In t (get_tasks s).
Proof.
  intros.
  apply tedge_inv in H.
  destruct H as (r, (H1, H2)).
  apply impedes_to_registered in H1.
  destruct H1 as (r', (H1, H3)).
  apply registered_to_blocked in H1.
  destruct H1 as (r'', H1).
  apply blocked_in_tasks in H1.
  assumption.
  apply Hwalk.
Qed.  

Lemma soundness_totally:
  TotallyDeadlocked s.
Proof.
  intros.
  unfold TotallyDeadlocked.
  intros.
  destruct H as (H, H0).
  assert (Hblk := H0).
  (* Task t is connected to another task, get t': *)
  apply blocked_in_waits in H0.
  apply in_waits_to_edge in H0.
  destruct H0 as (t', H0).
  exists t'. (* we've found t' *)
  intuition.
  + (* show that t' in dom T *)
    apply in_inv_left in H0;
    intuition.
  + apply tedge_inv in H0.
    *  destruct H0 as (r', (Hi, Hw)).
       rewrite <- blocked_eq_waits_for in Hw.
       assert (Heq : r = r').
         apply blocked_fun with (s:=s) (t:=t); r_auto.
       (* end assert *)
       subst.
       rewrite <- impedes_eq_registered; r_auto.
    * inversion is_cycle; r_auto.
Qed.
End TotallyDeadlockedSoundness.

Section Soundness.
Variable w:t_walk d.

Variable is_cycle: TCycle d w.
Let split := (fun t (p:prog) => mem_walk tid TID.eq_dec t w).

Let deadlocked := Map_TID_Props.partition split (get_tasks s).

Let Hdeadlocked: Map_TID_Props.Partition (get_tasks s) (fst deadlocked) (snd deadlocked).
Proof.
  apply Map_TID_Props.partition_Partition with (f:=split).
  auto with *.
  unfold deadlocked.
  auto.
Qed.
Check soundness_totally.
End Soundness.

End Correctness.

