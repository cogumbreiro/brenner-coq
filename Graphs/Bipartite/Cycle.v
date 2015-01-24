Require
  Graphs.Bipartite.Core
  Graphs.Bipartite.Main.

Module C := Graphs.Bipartite.Core.
Module M := Graphs.Bipartite.Main.

Require Import TacticsUtil Graphs.Core.

Section CycleAAtoBB.
Variable A : Type.
Variable B : Type.
Variable AB : A -> B -> Prop.
Variable BA : B -> A -> Prop.

Let G := M.mk_bipartite A B AB BA.

Notation b_edge := (M.b_edge G).
Notation a_edge := (M.a_edge G).
Notation a_walk := (M.a_walk G).
Notation b_walk := (M.b_walk G).
Notation BWalk := (M.BWalk G).
Notation AWalk := (M.AWalk G).
Notation ACycle := (M.ACycle G).
Notation BCycle := (M.BCycle G).
Notation ABA := (M.ABA G).
Notation BAB := (M.BAB G).
Notation BB := (M.BB G).
Notation AA := (M.AA G).

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
  apply C.aba_to_bab with (a1:=a1) (a3:=a3); r_auto.
  apply C.bab_to_b in H2; r_auto.
Qed.

Lemma edge_a_to_b_total:
  forall a1 a2 a3,
  AA (a1, a2) ->
  AA (a2, a3) ->
  exists b1 b2,
  edge_a_to_b (a1, a2) (a2, a3) (b1, b2).
Proof.
  intros.
  apply C.a_edge_to_bi_edge in H.
  apply C.a_edge_to_bi_edge in H0.
  destruct H as (b1, (H1, H2)).
  destruct H0 as (b2, (H3, H4)).
  exists b1.
  exists b2.
  intuition.
  apply edge_a_to_b_def.
  apply_auto C.ab_ba_to_aba.
  apply_auto C.ba_ab_to_bab.
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
    a_to_b (e1 :: e2 :: aw)%list (e :: bw)%list.

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
  AWalk ((a1, a2) :: nil) ->
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
  apply C.aba_to_bab with (a1:=a1) (a3:=a3); r_auto.
Qed.

Lemma edge_t_to_to_a_to_b:
  forall a1 a2 a3 b1 b2,
  edge_a_to_b (a1, a2) (a2, a3) (b1, b2) ->
  a_to_b ((a1, a2) :: ((a2, a3) :: nil)%list)%list ((b1, b2) :: nil)%list.
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
  - apply C.aba_to_b with (a1:=a1) (a2:=a2) (a3:=a3); r_auto.
  - compute; auto.
Qed.

Lemma a_to_b_cons_trt:
  forall a1 a2 a3 a4 aw b1 b2 b3 bw,
  ABA a1 b1 a2 ->
  ABA a2 b2 a3 ->
  a_to_b ((a2, a3) :: ((a3, a4) :: aw)%list)%list ((b2, b3) :: bw)%list
  ->
  a_to_b ((a1, a2) :: ((a2, a3) :: (a3, a4) :: aw)%list)%list
  ((b1, b2) :: ((b2, b3) :: bw)%list)%list.
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
  a_to_b ((a2, a3) :: ((a3, a4) :: aw))%list ((b2, b3) :: bw)%list
  ->
  a_to_b ((a1, a2) :: ((a2, a3) :: (a3, a4) :: aw)%list)%list
  ((b1, b2) :: ((b2, b3) :: bw)%list)%list
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
    apply C.a_to_aba in H3; destruct H3 as (r0, H3).
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
  a_to_b aw ((b1,b2)::bw)%list ->
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
  a_to_b ((a1,a2)::(a2,a3)::nil)%list ((b1,b2)::nil)%list ->
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
  a_to_b aw ((b1, b2) :: nil)%list ->
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
  a_to_b ((a1,a2)::(a2,a3)::nil)%list ((b1,b2)::nil)%list /\
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
  apply C.a_to_aba in H.
  destruct H as (r, H).
  apply C.aba_refl in H.
  apply C.bab_to_b in H.
  exists ((r,r) :: nil)%list.
  simpl in *.
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
      assert (H':= end_total (b1, b2) bw).
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
      apply C.aba_to_bab with (a1:=tn) (a3:=a2).
      assumption.
      apply edge_a_to_b_inv1 in H9.
      assumption.
    (* Ready to build the path *)
    exists ((rn,b1)::(b1,b2)::bw)%list.
    apply cycle_def with (vn:=r).
    apply end_cons. assumption.
    apply walk_cons. assumption.
    apply C.bab_to_b with (a:=a1). assumption.
    compute. trivial.
    assumption.
    assumption.
Qed.
End CycleAAtoBB.


Definition cycle_a_to_cycle_b := fun (bp:M.Bipartite) =>
  cycle_a_to_b
    (M.vertex_a bp) 
    (M.vertex_b bp)
    (M.AB bp)
    (M.BA bp).

Let cycle_b_to_cycle_a' := fun (bp:M.Bipartite) =>
  cycle_a_to_b
    (M.vertex_b bp)
    (M.vertex_a bp)
    (M.BA bp)
    (M.AB bp).

Lemma cycle_b_to_cycle_a :
  forall bp w,
  M.BCycle bp w ->
  exists w',
  M.ACycle bp w'.
Proof.
  intros.
  simpl in *.
  rewrite C.cycle_b_aa_eq_bb in H.
  assert (H':= cycle_b_to_cycle_a' bp w H).
  destruct H' as (w', H').
  exists w'.
  simpl in *.
  rewrite C.cycle_b_aa_eq_bb in H'.
  assumption.
Qed.
