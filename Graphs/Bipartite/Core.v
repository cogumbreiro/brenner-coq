Require Import Graphs.Core TacticsUtil.

Section Bipartite.
Variable a_vertex:Type.
Variable b_vertex:Type.
Notation a_edge:= ((a_vertex * a_vertex) % type).
Notation b_edge:= ((b_vertex * b_vertex) % type).

Variable AB : a_vertex -> b_vertex -> Prop.
Variable BA : b_vertex -> a_vertex -> Prop.


Inductive AA : a_edge -> Prop :=
  aa :
    forall a1 b a2,
    AB a1 b ->
    BA b a2 ->
    AA (a1, a2).

Inductive BB : b_edge -> Prop :=
  bb :
    forall b1 a b2,
    BA b1 a ->
    AB a b2 ->
    BB (b1, b2).

Notation AWalk := (Walk AA).
Notation ACycle := (Cycle AA).
Notation a_walk := (list a_edge).

Notation BWalk := (Walk BB).
Notation BCycle := (Cycle BB).
Notation b_walk := (list b_edge).

Inductive bi_vertex :=
  | bi_b_vertex : b_vertex -> bi_vertex
  | bi_a_vertex : a_vertex -> bi_vertex.

Notation bi_edge := (bi_vertex * bi_vertex) % type.
Notation bi_walk := (list bi_edge) % type.
Notation ba := (fun b a => ((bi_b_vertex b), (bi_a_vertex a))).
Notation ab := (fun a b => ((bi_a_vertex a), (bi_b_vertex b))).

Inductive BAEdge : bi_edge -> Prop :=
  ba_edge :
    forall b a,
    BA b a ->
    BAEdge ((bi_b_vertex b), (bi_a_vertex a)).

Inductive ABEdge : bi_edge -> Prop :=
  ab_edge :
    forall a b,
    AB a b ->
    ABEdge ((bi_a_vertex a), (bi_b_vertex b)).

Definition BiEdge (e:bi_edge) :=
  ABEdge e \/ BAEdge e.

Lemma ab_to_bi_edge:
  forall a b,
  AB a b ->
  BiEdge (ab a b).
Proof.
  intros.
  apply ab_edge in H.
  unfold BiEdge.
  auto.
Qed.

Lemma ba_to_bi_edge:
  forall b a,
  BA b a ->
  BiEdge (ba b a).
Proof.
  intros.
  apply ba_edge in H.
  unfold BiEdge.
  auto.
Qed.

Notation BiWalk := Walk BiEdge.
Notation BiCycle := Cycle BiEdge.

Lemma a_edge_to_bi_edge:
  forall a1 a2,
  AA (a1, a2) ->
  exists b,
  AB a1 b /\ BA b a2.
Proof.
  intros.
  inversion H.
  exists b.
  intuition.
Qed.

Lemma bi_edge_to_a_edge:
  forall a1 b a2,
  AB a1 b ->
  BA b a2 ->
  AA (a1, a2).
Proof.
  intros.
  apply aa with (b:=b); r_auto.
Qed.

Lemma b_edge_to_bi_edge:
  forall b1 b2,
  BB (b1, b2) ->
  exists a,
  BA b1 a /\ AB a b2.
Proof.
  intros.
  inversion H.
  exists a.
  intuition.
Qed.

Lemma bi_edge_to_b_edge:
  forall b1 a b2,
  BA b1 a ->
  AB a b2 ->
  BB (b1, b2).
Proof.
  intros.
  apply bb with (a:=a); r_auto.
Qed.

Definition BAB (b1:b_vertex) (a:a_vertex) (b2:b_vertex) :=
  BA b1 a /\ AB a b2.

Lemma ba_ab_to_bab:
  forall b1 a b2,
  BA b1 a ->
  AB a b2 ->
  BAB b1 a b2.
Proof.
  unfold BAB. auto.
Qed.

Definition ABA (a1:a_vertex) (b:b_vertex) (a2:a_vertex) :=
  AB a1 b /\ BA b a2.

Lemma ab_ba_to_aba:
  forall a1 b a2,
  AB a1 b ->
  BA b a2 ->
  ABA a1 b a2.
Proof.
  unfold ABA. auto.
Qed.

Lemma bab_to_b:
  forall b1 a b2,
  BAB b1 a b2 ->
  BB (b1, b2).
Proof.
  intros.
  destruct H.
  apply bi_edge_to_b_edge with (a:=a); r_auto.
Qed.

Lemma b_to_bab:
  forall b1 b2,
  BB (b1, b2) ->
  exists a,
  BAB b1 a b2.
Proof.
  intros.
  unfold BAB.
  apply_auto b_edge_to_bi_edge.
Qed.    

Lemma aba_to_aa :
  forall a1 b a2,
  ABA a1 b a2 ->
  AA (a1, a2).
Proof.
  intros.
  destruct H.
  apply bi_edge_to_a_edge with (b:=b); r_auto.
Qed.

Lemma a_to_aba:
  forall a1 a2,
  AA (a1, a2) ->
  exists b,
  ABA a1 b a2.
Proof.
  intros.
  unfold ABA.
  apply_auto a_edge_to_bi_edge.
Qed.    

Lemma bab_to_aba:
  forall b1 a1 b2 a2 b3,
  BAB b1 a1 b2 ->
  BAB b2 a2 b3 ->
  ABA a1 b2 a2.
Proof.
  intros.
  destruct H.
  destruct H0.
  unfold ABA.
  auto.
Qed.

Lemma aba_to_bab:
  forall a1 b1 a2 b2 a3,
  ABA a1 b1 a2 ->
  ABA a2 b2 a3 ->
  BAB b1 a2 b2.
Proof.
  intros.
  destruct H.
  destruct H0.
  unfold BAB.
  auto.
Qed.

Lemma aba_to_b:
  forall a1 a2 a3 b1 b2,
  ABA a1 b1 a2 ->
  ABA a2 b2 a3 ->
  BB (b1, b2).
Proof.
  intros.
  assert (H2: BAB b1 a2 b2).
  + apply aba_to_bab with (a1:=a1) (a3:=a3); r_auto.
  + apply bab_to_b with (a:=a2); r_auto.
Qed.

Lemma bab_to_aa :
  forall b1 b2 b3 a1 a2,
  BAB b1 a1 b2 ->
  BAB b2 a2 b3 ->
  AA (a1, a2).
Proof.
  intros.
  assert (H2: ABA a1 b2 a2).
  + apply bab_to_aba with (b1:=b1) (b3:=b3); r_auto.
  + apply aba_to_aa with (b:=b2); r_auto.
Qed.

Lemma aba_refl:
  forall a b,
  ABA a b a ->
  BAB b a b.
Proof.
  intros.
  assert (H1:= aba_to_bab _ _ _ _ _ H H).
  assumption.
Qed.

Lemma bab_refl:
  forall b a,
  BAB b a b ->
  ABA a b a.
Proof.
  intros.
  assert (H1:= bab_to_aba _ _ _ _ _ H H).
  assumption.
Qed.

Section CycleAAtoBB.

Inductive edge_a_to_b : a_edge -> a_edge -> b_edge -> Prop :=
  edge_a_to_b_def:
    forall a1 a2 a3 b1 b2,
    ABA a1 b1 a2 ->
    ABA a2 b2 a3 ->
    edge_a_to_b (a1, a2) (a2, a3) (b1, b2).

Lemma a_to_b_b_edge:
  forall e1 e2 e3,
  edge_a_to_b e1 e2 e3 ->
  BB e3.
Proof.
  intros.
  inversion H.
  subst.
  assert (H2: BAB b1 a2 b2).
  apply aba_to_bab with (a1:=a1) (a3:=a3); r_auto.
  apply bab_to_b in H2; r_auto.
Qed.
 
Lemma edge_a_to_b_total:
  forall a1 a2 a3,
  AA (a1, a2) ->
  AA (a2, a3) ->
  exists b1 b2,
  edge_a_to_b (a1, a2) (a2, a3) (b1, b2).
Proof.
  intros.
  apply a_edge_to_bi_edge in H.
  apply a_edge_to_bi_edge in H0.
  destruct H as (b1, (H1, H2)).
  destruct H0 as (b2, (H3, H4)).
  exists b1.
  exists b2.
  intuition.
  apply edge_a_to_b_def.
  unfold ABA. auto.
  unfold ABA. auto.
Qed.

Inductive a_to_b : a_walk -> b_walk -> Prop :=
  | a_to_b_nil:
    a_to_b nil nil
  | t_to_b_edge_nil:
    forall e,
    a_to_b (e::nil)%list nil
  | a_to_b_cons:
    forall e1 e2 e aw bw,
    a_to_b (e2 :: aw)%list bw ->
    edge_a_to_b e1 e2 e ->
    a_to_b (e1 :: e2 :: aw)%list (e :: bw).

Lemma a_to_b_total_nil:
  exists bw : b_walk, a_to_b nil bw /\ BWalk bw.
Proof.
  exists nil.
  intuition.
  apply a_to_b_nil.
  apply walk_nil.
Qed.

Lemma a_to_b_total_edge:
  forall a1 a2,
  AWalk ((a1, a2) :: nil)%list ->
  exists bw : b_walk, a_to_b ((a1, a2) :: nil)%list bw /\ BWalk bw.
Proof.
  exists nil.
  intuition.
  apply t_to_b_edge_nil.
  apply walk_nil.  
Qed.

Lemma a_walk_to_edge_a_to_b:
  forall a1 a2 a3 aw,
  AWalk ((a1, a2) :: ((a2, a3) :: aw)%list) ->
  exists b1 b2, edge_a_to_b (a1, a2) (a2, a3) (b1, b2).
Proof.
  intros.
  inversion H; subst.
  inversion H2; subst.
  apply_auto edge_a_to_b_total.
Qed.

Lemma edge_a_to_b_inv1:
  forall a1 a2 a3 b1 b2,
  edge_a_to_b (a1, a2) (a2, a3) (b1, b2) ->
  ABA a1 b1 a2.
Proof.
  intros. inversion H.
  assumption.
Qed.

Lemma edge_a_to_b_inv2:
  forall a1 a2 a3 b1 b2,
  edge_a_to_b (a1, a2) (a2, a3) (b1, b2) ->
  ABA a2 b2 a3.
Proof.
  intros. inversion H.
  assumption.
Qed.

Lemma edge_a_to_b_inv3:
  forall a1 a2 a3 b1 b2,
  edge_a_to_b (a1, a2) (a2, a3) (b1, b2) ->
  BAB b1 a2 b2.
Proof.
  intros. inversion H.
  apply aba_to_bab with (a1:=a1) (a3:=a3); r_auto.
Qed.

Lemma edge_t_to_to_a_to_b:
  forall a1 a2 a3 b1 b2,
  edge_a_to_b (a1, a2) (a2, a3) (b1, b2) ->
  a_to_b ((a1, a2) :: ((a2, a3) :: nil)%list)%list ((b1, b2) :: nil).
Proof.
  intros.
  inversion H.
  apply a_to_b_cons.
  apply t_to_b_edge_nil.
  apply edge_a_to_b_def; r_auto.
Qed.

Lemma b_walk_cons_trt:
  forall r0 b1 b2 a1 a2 a3 bw,
  ABA a1 r0 a2 ->
  ABA a2 b1 a3 ->
  BWalk ((b1, b2) :: bw) ->
  BWalk ((r0, b1) :: ((b1, b2) :: bw)%list).
Proof.
  intros.
  inversion H0; subst.
  apply walk_cons.
  - assumption.
  - apply aba_to_b with (a1:=a1) (a2:=a2) (a3:=a3); r_auto.
  - compute; auto.
Qed.

Lemma a_to_b_cons_trt:
  forall a1 a2 a3 a4 aw b1 b2 b3 bw,
  ABA a1 b1 a2 ->
  ABA a2 b2 a3 ->
  a_to_b ((a2, a3) :: ((a3, a4) :: aw)%list)%list ((b2, b3) :: bw)
  ->
  a_to_b ((a1, a2) :: ((a2, a3) :: (a3, a4) :: aw)%list)%list
  ((b1, b2) :: ((b2, b3) :: bw)%list).
Proof.
  intros.
  assert (H5': edge_a_to_b (a1, a2) (a2, a3) (b1, b2)).
  * apply_auto edge_a_to_b_def.
  * apply_auto a_to_b_cons.
Qed.

Lemma a_to_b_b_walk_cons:
  forall a1 a2 a3 a4 aw b1 b2 b3 bw,
  ABA a1 b1 a2 ->
  ABA a2 b2 a3 ->
  BWalk ((b2, b3) :: bw) ->
  edge_a_to_b (a2, a3) (a3, a4) (b2, b3) ->
  a_to_b ((a2, a3) :: ((a3, a4) :: aw))%list ((b2, b3) :: bw)
  ->
  a_to_b ((a1, a2) :: ((a2, a3) :: (a3, a4) :: aw)%list)%list
  ((b1, b2) :: ((b2, b3) :: bw)%list)
  /\
  BWalk ((b1, b2) :: ((b2, b3) :: bw)%list).
Proof.
  intuition.
  + apply_auto a_to_b_cons_trt.
  + apply edge_a_to_b_inv1 in H2.
    apply b_walk_cons_trt with (a1:=a1) (a2:=a2) (a3:=a3); r_auto.
Qed.

Lemma edge_a_to_b_to_b_walk:
  forall a1 a2 a3 b1 b2,
  edge_a_to_b (a1, a2) (a2, a3) (b1, b2) ->
  BWalk ((b1, b2) :: nil).
Proof.
  intros.
  apply walk_cons.
  * apply walk_nil.
  * apply a_to_b_b_edge in H.
    assumption.
  * compute;
    auto.
Qed.

Lemma a_to_b_total_step:
  forall a1 a2 a3 aw bw,
  AWalk ((a1, a2) :: ((a2, a3) :: aw)%list) ->
  a_to_b ((a2, a3) :: aw)%list bw ->
  BWalk bw ->
  exists bw' : b_walk,
  a_to_b ((a1, a2) :: ((a2, a3) :: aw)%list)%list bw' /\ BWalk bw'.
Proof.
  intros.
  assert (H3: AA (a1, a2)).
  inversion H; subst; assumption.
  inversion H0.
  - (* Case 1: *)
    subst.
    assert (Hr := H).
    apply a_walk_to_edge_a_to_b in Hr.
    destruct Hr as (b1, (b2, Hr)).
    exists (cons (b1, b2) nil).
    intuition.
    + apply_auto a_to_b_cons.
    + apply edge_a_to_b_to_b_walk with (a1:=a1) (a2:=a2) (a3:=a3); r_auto.
  - (* Case 2: *)
    subst.
    destruct e2 as (a3', a4).
    inversion H7; subst. (* a3 = a3' *)
    apply a_to_aba in H3; destruct H3 as (r0, H3).
    exists ((r0, b1) :: (b1, b2):: bw0)%list.
    apply_auto a_to_b_b_walk_cons.
Qed.

Lemma a_to_b_total:
  forall aw,
  AWalk aw ->
  exists bw, a_to_b aw bw /\ BWalk bw.
Proof.
  intros.
  induction aw.
  - apply a_to_b_total_nil.
  - inversion H.
    subst.
    apply IHaw in H2; clear IHaw.
    destruct H2 as (bw, (H1, H2)).
    destruct a as (a1, a2).
    destruct aw.
    + apply_auto a_to_b_total_edge.
    + destruct p as (a2', a3).
      (* a2 = a2' *)
      compute in H4; rewrite <- H4 in *; clear H4.
      apply a_to_b_total_step with (bw := bw); r_auto.
Qed.

Lemma a_to_b_step:
  forall aw b1 b2 bw,
  AWalk aw ->
  a_to_b aw ((b1,b2)::bw) ->
  BWalk ((b1,b2)::bw) ->
  exists a1 a2 a3 aw',
  (aw = ((a1,a2)::(a2,a3)::aw')%list /\ 
  ABA a1 b1 a2 /\ ABA a2 b2 a3).
Proof.
  intros.
  inversion H0.
  - subst.
    destruct e1 as (a1,a2).
    destruct e2 as (a2',a3).
    exists a1;
    exists a2;
    exists a3;
    exists aw0.
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

Lemma a_to_b_mk_nil:
  forall a1 a2 a3 b1 b2,
  a_to_b ((a1,a2)::(a2,a3)::nil)%list ((b1,b2)::nil) ->
  (ABA a1 b1 a2 /\ ABA a2 b2 a3).
Proof.
  intros.
  inversion H.
  subst.
  inversion H6.
  subst.
  auto.
Qed.

Lemma a_to_b_nil_inv:
  forall aw b1 b2,
  a_to_b aw ((b1, b2) :: nil) ->
  exists a1 a2 a3,
  aw = ((a1, a2) :: (a2, a3) :: nil)%list /\
  edge_a_to_b (a1, a2) (a2, a3) (b1, b2).
Proof.
  intros.
  inversion H.
  subst.
  destruct e1 as (a1, a2').
  destruct e2 as (a2, a3).
  inversion H4.
  subst.
  exists a1; exists a2; exists a3.
  intuition.
  inversion H3.
  auto.
Qed.

Lemma a_to_b_end:
  forall aw bw b1 b2,
  End bw (b1,b2) ->
  a_to_b aw bw ->
  exists a1 a2 a3,
  a_to_b ((a1,a2)::(a2,a3)::nil)%list ((b1,b2)::nil) /\
  ABA a1 b1 a2 /\ ABA a2 b2 a3 /\ End aw (a2, a3).
Proof.
  intros.
  induction H0.
  - inversion H.
  - inversion H.
  - destruct bw.
    + inversion H0.
      subst.
      destruct e1 as (a1, a2'); destruct e2 as (a2, a3); destruct e as (b1', b2').
      inversion H1.
      subst.
      apply end_inv in H.
      inversion H. subst; clear H.
      exists a1; exists a2; exists a3.
      intuition.
      apply_auto edge_t_to_to_a_to_b.
      apply end_cons.
      apply end_nil.
    + inversion H; subst; clear H.
      apply IHa_to_b in H5.
      destruct H5 as (a1, (a2, (a3, (Ha, (Hb, (Hc, Hd)))))).
      exists a1; exists a2; exists a3.
      intuition.
      apply end_cons.
      assumption.
Qed.

Lemma cycle_a_to_b1:
  forall t,
  AA (t, t) ->
  exists w', BCycle w'.
Proof.
  intros.
  apply a_to_aba in H.
  destruct H as (r, H).
  apply aba_refl in H.
  apply bab_to_b in H.
  exists ((r,r) :: nil)%list.
  apply_auto edge1_to_cycle.
Qed.

Theorem cycle_a_to_b:
  forall w,
  ACycle w ->
  exists w', BCycle w'.
Proof.
  intros.
  expand H. (* ACycle w *)
  rename v1 into a1;
  rename v2 into a2;
  rename vn into tn.
  inversion H1; subst. (* AWalk ((v1, v2) :: w0) *)
  apply a_to_b_total in H1.
  destruct H1 as (bw, (H1, H2)).
  inversion H1.
  - (* Case: (t,t)::nil *)
    subst.
    apply end_inv in H0; inversion H0; subst.
    apply cycle_a_to_b1 with (t:=tn); r_auto.
  - (* Case: (a1,a2) :: aw *)
    subst.
    destruct e2 as (a2', a3).
    compute in H5; subst; rename a2' into a2. (* a2' = a2 *)
    destruct e as (b1, b2).
    (* Fun begins *)
    rename bw0 into bw.
    assert (Hre: exists r rn, End ((b1, b2) :: bw) (r, rn) ).
      assert (H':= end_total _ (b1, b2) bw).
      destruct H' as ((rn,b1'), H').
      exists rn; exists b1'.
      assumption.
    destruct Hre as (r, (rn, Hre)).
    assert (Hre' := Hre).
    apply a_to_b_end with (aw := ((a1, a2) :: ((a2, a3) :: aw)%list)%list) in Hre.
    destruct Hre as (t, (tn', (a1', (Ha, (Hb, (Hc, Hd)))))).
    apply end_det with (e:=(tn, a1)) in Hd.
    expand Hd. rename tn' into tn; rename a1' into a1.
    assert (Hs: BAB rn a1 b1).
      apply aba_to_bab with (a1:=tn) (a3:=a2).
      assumption.
      apply edge_a_to_b_inv1 in H9.
      assumption.
    (* Ready to build the path *)
    exists ((rn,b1)::(b1,b2)::bw)%list.
    apply cycle_def with (vn:=r).
    apply end_cons. assumption.
    apply walk_cons. assumption.
    apply bab_to_b with (a:=a1). assumption.
    compute. trivial.
    assumption.
    assumption.
Qed.
End CycleAAtoBB.

Section CycleAtoC.

Inductive edge_a_to_c : a_edge -> bi_edge -> bi_edge -> Prop :=
  edge_a_to_c_def:
    forall a1 b a2,
    ABA a1 b a2 ->
    edge_a_to_c (a1, a2) (ab a1 b) (ba b a2).

Lemma edge_a_to_c_inv1:
  forall e1 e2 e3,
  edge_a_to_c e1 e2 e3 ->
  AA e1.
Proof.
  intros.
  inversion H.
  apply aba_to_aa with (b:=b); r_auto.
Qed.

Lemma edge_a_to_c_inv2:
  forall e1 e2 e3,
  edge_a_to_c e1 e2 e3 ->
  BiEdge e2.
Proof.
  intros.
  inversion H.
  unfold ABA in H0.
  destruct H0 as (H0,_).
  apply_auto ab_to_bi_edge.
Qed.

Lemma edge_a_to_c_inv3:
  forall e1 e2 e3,
  edge_a_to_c e1 e2 e3 ->
  BiEdge e3.
Proof.
  intros.
  inversion H.
  unfold ABA in H0.
  destruct H0 as (_,H0).
  apply_auto ba_to_bi_edge.
Qed.

Inductive a_to_c : a_walk -> bi_walk -> Prop :=
  | a_to_c_nil:
    a_to_c nil nil
  | a_to_c_cons:
    forall e1 e2 e aw cw,
    a_to_c aw cw ->
    edge_a_to_c e e1 e2 ->
    a_to_c (e :: aw)%list (e1 :: e2 :: cw)%list.


Lemma aa_to_edge_a_to_c:
  forall a1 a2,
  AA (a1, a2) ->
  exists b, edge_a_to_c (a1, a2) (ab a1 b) (ba b a2).
Proof.
  intros.
  inversion H.
  subst.
  exists b.
  apply edge_a_to_c_def.
  unfold ABA.
  auto.
Qed.

Let a_to_c_total_1:
  forall a1 a2,
  AA (a1, a2) ->
  exists cw : bi_walk, a_to_c ((a1, a2) :: nil) cw /\ BiWalk cw.
Proof.
  intros.
  apply aa_to_edge_a_to_c in H; r_auto.
  destruct H as (b, H).
  exists ((ab a1 b)::(ba b a2)::nil)%list.
  intuition.
  - apply a_to_c_cons.
    + apply a_to_c_nil.
    + assumption.
  - inversion H; subst.
    unfold ABA in H1.
    destruct H1 as (H1, H2).
    apply ab_to_bi_edge in H1.
    apply ba_to_bi_edge in H2.
    apply_auto edge2_to_walk.
Qed.

Let a_to_c_total_2:
  forall a1 a2 a3 aw cw,
  AWalk ((a1, a2) :: ((a2, a3) :: aw)%list) ->
  a_to_c ((a2, a3) :: aw)%list cw ->
  BiWalk cw ->
  exists cw' : bi_walk,
  a_to_c ((a1, a2) :: ((a2, a3) :: aw)%list)%list cw' /\ BiWalk cw'.
Proof.
  intros.
  assert (H3: AA (a1, a2)).
  inversion H; subst; assumption.
  inversion H0.
  subst.
  assert (Hr := H).
  inversion H7; subst; clear H9. (* expand: e1 e2 *)
  apply aa_to_edge_a_to_c in H3; destruct H3 as (b1, H3).
  rename b into b2.
  exists (cons (ab a1 b1)
         (cons (ba b1 a2)
         (cons (ab a2 b2)
         (cons (ba b2 a3) cw0)))).
  intuition.
  + apply_auto a_to_c_cons.
  + apply walk_cons2.
    apply edge_a_to_c_inv2 in H3.
    assumption.
    apply walk_cons2.
    apply edge_a_to_c_inv3 in H3.
    assumption.
    assumption.
Qed.

Lemma a_to_c_total:
  forall aw,
  AWalk aw ->
  exists cw, a_to_c aw cw /\ BiWalk cw.
Proof.
  intros.
  induction aw.
  - exists nil.
    intuition.
    + apply a_to_c_nil.
    + apply walk_nil.
  - inversion H.
    subst.
    apply IHaw in H2; clear IHaw.
    destruct H2 as (cw, (H1, H2)).
    destruct a as (a1, a2).
    destruct aw.
    + apply_auto a_to_c_total_1.
    + destruct p as (a2', a3).
      (* a2 = a2' *)
      compute in H4; rewrite <- H4 in *; clear H4.
      apply a_to_c_total_2 with (cw := cw); r_auto.
Qed.

Let cycle_a_to_c1:
  forall a,
  AA (a, a) ->
  exists w', BiCycle w'.
Proof.
  intros.
  apply a_to_aba in H.
  destruct H as (b, H).
  unfold ABA in H.
  destruct H as (H1, H2).
  apply ab_to_bi_edge in H1.
  apply ba_to_bi_edge in H2.
  exists (cons (ab a b)
         (cons (ba b a) nil)).
  apply_auto edge2_to_cycle.
Qed.


Lemma a_to_c_end:
  forall aw a1 a2 cw e,
  End aw (a1, a2) ->
  End cw e ->
  a_to_c aw cw ->
  exists b,
  a_to_c ((a1,a2)::nil)%list ((ab a1 b)::(ba b a2)::nil)%list
  /\ e = (ba b a2).
Proof.
  intros.
  induction H1.
  - inversion H0.
  - destruct cw.
    + expand H1. (* aw = nil *)
      expand H2. (* e0 = (a1, a2); e1 = (a1, b); e2 = (b, a2) *)
      apply end_inv in H; expand H.
      exists b.
      intuition.
      * apply a_to_c_cons.
        apply a_to_c_nil.
        apply_auto edge_a_to_c_def.
      * expand H0.
        apply end_inv in H4.
        auto.
    + destruct aw.
      * inversion H1.
      * apply end_inv_cons in H.
        apply IHa_to_c in H; clear IHa_to_c.
        assumption.
        repeat (apply end_inv_cons in H0).
        assumption.
Qed.

Theorem cycle_a_to_c:
  forall w,
  ACycle w ->
  exists w', BiCycle w'.
Proof.
  intros.
  expand H. (* ACycle w *)
  rename v1 into a1;
  rename v2 into a2;
  rename vn into an.
  inversion H1; subst. (* AWalk ((v1, v2) :: w0) *)
  apply a_to_c_total in H1.
  destruct H1 as (bw, (H1, H2)).
  expand H1.
  destruct w0.
  - (* Case: (a,a)::nil *)
    subst.
    apply end_inv in H0; inversion H0; subst.
    apply cycle_a_to_c1 with (a:=an); r_auto.
  - (* Case: (a1,a2) :: aw *)
    subst.
    inversion H9; subst.
    destruct H10 as (H10, H11).
    destruct p as (a2', a3);
    compute in H5; subst; rename a2' into a2. (* a2' = a2 *)
    (* Fun begins *)
    remember ((bi_a_vertex a1, bi_b_vertex b)
        :: ((bi_b_vertex b, bi_a_vertex a2) :: cw)%list)%list as w.
    (* Hend := BiEnd w e *)
    assert (Hend: exists e, End w e).
      assert (H':= end_total _ (bi_a_vertex a1, bi_b_vertex b) ((bi_b_vertex b, bi_a_vertex a2) :: cw)).
      subst.
      assumption.
    (* Hend *)
    destruct Hend as (e, Hend).
    assert (Hatoc := Hend).
    remember ((a1, a2) :: ((a2, a3) :: w0))%list as aw.
    apply a_to_c_end with (aw:= aw) (a1:=an) (a2:=a1) in Hatoc.
    + destruct Hatoc as (bn, (Hac, Heqe)).
      destruct e. inversion Heqe; rewrite H1 in *; rewrite H5 in *; clear Heqe H1 H5.
      exists w.
      (*
      exists (cons (ab an bn)
             (cons (ba bn a1) w)).*)
      subst.
      apply cycle_def with (vn:=(bi_b_vertex bn)); r_auto.
    + assumption.
    + subst; apply_auto a_to_c_cons.
Qed.

End CycleAtoC.
End Bipartite.

Implicit Arguments AA.
Implicit Arguments BB.
Implicit Arguments BAB.
Implicit Arguments ABA.

Lemma aa_eq_bb:
  forall {A} {B} AB BA e,
  @AA A B AB BA e <-> BB BA AB e.
Proof.
  intros.
  intuition.
  - inversion H. apply bb with (a:=b0); r_auto.
  - inversion H. apply aa with (b:=a0); r_auto.
Qed.

Lemma walk_a_aa_eq_bb:
  forall {A} {B} AB BA w,
  Walk (@AA A B AB BA) w <-> Walk (BB BA AB) w.
Proof.
  intros.
  induction w.
  - intuition; repeat (apply walk_nil).
  - intuition.
    + inversion H1.
      subst.
      apply H in H4.
      apply aa_eq_bb in H5.
      apply_auto walk_cons.
    + inversion H1; subst.
      apply H0 in H4.
      apply aa_eq_bb in H5.
      apply_auto walk_cons.
Qed.

Lemma walk_b_aa_eq_bb:
  forall {A} {B} AB BA w,
  Walk (@BB A B BA AB) w <-> Walk (AA AB BA) w.
Proof.
  intros.
  induction w.
  - intuition; repeat (apply walk_nil).
  - intuition.
    + inversion H1.
      subst.
      apply H in H4.
      apply aa_eq_bb in H5.
      apply_auto walk_cons.
    + inversion H1; subst.
      apply H0 in H4.
      apply aa_eq_bb in H5.
      apply_auto walk_cons.
Qed.

Lemma cycle_a_aa_eq_bb:
  forall {A} {B} AB BA w,
  Cycle (@AA A B AB BA) w <-> Cycle (BB BA AB) w.
Proof.
  intros.
  intuition.
  - expand H.
    rewrite walk_a_aa_eq_bb in H1.
    apply cycle_def with (vn:=vn); r_auto.
  - expand H.
    rewrite walk_b_aa_eq_bb in H1.
    apply cycle_def with (vn:=vn); r_auto.
Qed.

Lemma cycle_b_aa_eq_bb:
  forall {A} {B} AB BA w,
  Cycle (@BB A B BA AB) w <-> Cycle (AA AB BA) w.
Proof.
  intros.
  intuition.
  - expand H.
    rewrite walk_b_aa_eq_bb in H1.
    apply cycle_def with (vn:=vn); r_auto.
  - expand H.
    rewrite walk_a_aa_eq_bb in H1.
    apply cycle_def with (vn:=vn); r_auto.
Qed.
