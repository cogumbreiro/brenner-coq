Require Import Coq.FSets.FMapFacts.
Require Import Coq.FSets.FSetProperties.
Require Import SetUtil.
Require Import MapUtil.
Require Import ListUtil.

Set Implicit Arguments.

Section MATCH.

Variable K : Type.

Variable V : Type.

Variable key_eq_dec : forall x y : K, {x = y} + {x <> y}.

Variable value_eq_dec : forall x y : V, {x = y} + {x <> y}.

Definition match_key (k:K) (p:K*V) :=
  let (k', _) := p in
  if key_eq_dec k k' then true else false.

Let partition_in':
  forall k k' v l matched mismatched,
  partition (match_key k) l = (matched, mismatched) ->
  In (k', v) l ->
  {In (k',v) matched /\ k = k'} + {In (k',v) mismatched /\ k <> k'}.
Proof.
  intros.
  assert (Heq1 : matched = fst (partition (match_key k) l)).
  rewrite H; auto. (* eoa *)
  assert (Heq2 : mismatched = snd (partition (match_key k) l)).
  rewrite H; auto. (* eoa *)
  rewrite Heq1; rewrite Heq2.
  assert (Hdec: {In (k', v) (fst (partition (match_key k) l)) /\ match_key k (k',v) = true} +
{In (k', v) (snd (partition (match_key k) l)) /\ match_key k (k',v) = false}).
  apply partition_in.
  assumption.
  (* eoa *)
  destruct Hdec.
  - left.
    destruct a.
    simpl in *.
    destruct (key_eq_dec k k').
    subst.
    auto.
    inversion H2.
  - right.
    intuition.
    simpl in *.
    destruct (key_eq_dec k k').
    inversion H2.
    contradiction f.
Qed.

Let match_key_refl:
  forall k v,
  match_key k (k,v) = true.
Proof.
  intros.
  simpl.
  destruct (key_eq_dec k k).
  auto.
  contradiction n.
  trivial.
Qed.

Let partition_match_key_spec_1:
  forall v k l,
  In (k, v) l <-> In (k, v) (fst (partition (match_key k) l)).
Proof.
  intros.
  split.
  - intros.
    rewrite partition_iff_1.
    intuition.
  - intros.
    rewrite partition_iff_1 in H.
    intuition.
Qed.

Let match_key_subst:
  forall k k' v,
  match_key k (k', v) = true ->
  k = k'.
Proof.
  intros.
  simpl in *.
  destruct (key_eq_dec k k').
  assumption.
  inversion H.
Qed.

Let partition_match_key_spec_2:
  forall v k' k l,
  In (k', v) (fst (partition (match_key k) l)) ->
  k' = k.
Proof.
  intros.
  rewrite partition_iff_1 in H.
  destruct H as (_, H).
  apply match_key_subst in H.
  auto.
Qed.

Let partition_match_key_spec_3:
  forall v k l,
  In (k, v) l <-> In v (snd (split (fst (partition (match_key k) l)))).
Proof.
  intros.
  split.
  - intros.
    apply partition_match_key_spec_1 in H.
    apply in_split_r in H.
    auto.
  - intros.
    rewrite partition_match_key_spec_1.
    apply split_in_r in H.
    destruct H as (k', Hin).
    assert (H := Hin).
    apply partition_match_key_spec_2 in H.
    subst.
    assumption.
Qed.

Let in_split_r_2:
  forall {L R:Type}(lst:list (L * R)%type) (lst_l:list L) (lst_r:list R) (l:L) (r:R),
  split lst = (lst_l, lst_r) ->
  In (l, r) lst ->
  In r lst_r.
Proof.
  intros.
  assert (lst_r = snd (split lst)).
  rewrite H; auto. (* eoa *)
  rewrite H1.
  assert (r = snd (l, r)). auto. (* eoa *)
  rewrite H2.
  apply in_split_r.
  assumption.
Qed.

Let in_matched:
  forall k v ks vs l matched mismatched,
  In v vs ->
  split matched = (ks, vs) ->
  partition (match_key k) l = (matched, mismatched) ->
  In (k, v) (fst (partition (match_key k) l)).
Proof.
  intros.
  assert (In (k, v) (fst (partition (match_key k) l))).
  rewrite partition_iff_1.
  assert (In v (snd (split matched))).
  rewrite H0; auto. (* eoa *)
  clear H H0.
  intuition.
  rewrite partition_match_key_spec_3.
  rewrite H1.
  auto.
  assumption.
Qed.


Require Import Recdef. (* Required by Function *)
Require Import Coq.Arith.Wf_nat. (* Required implicitly by measure obligations *)

Function unproj (l:list (K*V)) {measure length l} : list (K * (list V)) :=
  match l with
    | e :: l' =>
      let (k, v) := e in
      let (matched, mismatched) := partition (match_key k) l' in
      let (_, vs) := split matched in
      (k, v :: vs)::(unproj mismatched)
    | nil => nil
  end.
Proof.
  intros.
  subst.
  assert (mismatched = (snd (partition (match_key k) l'))).
  rewrite teq1; auto.
  rewrite H.
  simpl.
  apply Lt.le_lt_n_Sm.
  apply partition_length.
Defined.

Theorem unproj_spec:
  forall k v l,
  (List.In (k, v) l <-> exists l', List.In (k, l') (unproj l) /\ In v l').
Proof.
  intros.
  functional induction (unproj l).
  - split.
    + intros.
      inversion H.
      * inversion H0; subst; clear H0 H.
        exists (v :: vs).
        intuition.
      * assert ({In (k,v) matched /\ k0 = k} + {In (k,v) mismatched /\ k0 <> k}).
        apply partition_in' with (k:=k0) (k':=k) (l:=l').
        auto.
        auto.
        (* eoa *)
        destruct H1 as [(H1, H2)|(H1, H2)].
        subst.
        exists (v0 :: vs).
        intuition.
        apply in_cons.
        apply in_split_r_2 with (lst:=matched) (lst_l:=_x) (l:=k); repeat auto.
        (* eoa *)
        apply IHl0 in H1.
        destruct H1 as (s, (Hin, Hin')).
        exists s.
        intuition.
     + intros.
       destruct H as (s, (Hin, Hin')).
       destruct Hin.
       * inversion H; subst; clear H.
         destruct (value_eq_dec v v0).
         subst; apply in_eq. (* end of eq *)
         apply in_cons.
         clear IHl0.
         apply in_cons_neq in Hin'.
         apply in_matched with (k:=k) (ks:=_x) (l:=l') (matched:=matched) (mismatched:=mismatched) in Hin'.
         apply partition_iff_1 in Hin'.
         intuition.
         auto.
         auto.
         auto.
       * assert (exists s', In (k, s') (unproj mismatched) /\ In v s').
         exists s; auto.
         apply IHl0 in H0. clear IHl0.
         apply in_cons.
         assert (In (k, v) (snd (partition (match_key k0) l'))).
         rewrite e2; auto. (* eoa *)
         apply partition_iff_2 in H1.
         intuition.
  - split.
    intros. inversion H.
    intros.
    destruct H as (s, (Hin, _)).
    inversion Hin.
Qed.

Let in_unproj_to_in:
  forall k v l l',
  List.In (k, l') (unproj l) ->
  In v l' ->
  List.In (k, v) l.
Proof.
  intros.
  assert (exists l', List.In (k, l') (unproj l) /\ In v l').
  exists l'.
  intuition.
  apply unproj_spec.
  assumption.
Qed.

Definition eq_key {A:Type} (p p':K*A) := (fst p) = (fst p').

Definition NotInA {A:Type} f (k:K) l := forall (v:A), ~ InA f (k, v) l.

Let ina_to_in:
  forall {A:Type} k (v:A) l,
  InA eq_key (k, v) l ->
  exists v', In (k, v') l.
Proof.
  intros.
  rewrite InA_altdef in H.
  rewrite Exists_exists in H.
  destruct H as ((k',v'), (Hin, Heq)).
  unfold eq_key in Heq.
  simpl in Heq; subst.
  exists v'.
  auto.
Qed.

Let in_to_ina:
  forall {A:Type} k (v:A) l,
  In (k, v) l ->
  InA eq_key (k, v) l.
Proof.
  intros.
  rewrite InA_altdef.
  rewrite Exists_exists.
  exists (k, v).
  intuition.
Qed.

Lemma unproj_absurd:
  forall k l,
  In (k, nil) (unproj l) -> False.
Proof.
  intros.
  functional induction (unproj l).
  - inversion H.
    + inversion H0.
    + apply IHl0.
      assumption.
  - inversion H.
Qed.

Let partition_match_key_spec_4:
  forall v k l,
  In (k, v) (snd (partition (match_key k) l)) -> False.
Proof.
  intros.
  rewrite partition_iff_2 in H.
  destruct H as (_, H).
  assert (Hm:= match_key_refl k v).
  rewrite Hm in H.
  inversion H.
Qed.

Let partition_match_key_spec_5:
  forall k l,
  NotInA eq_key k (snd (partition (match_key k) l)).
Proof.
  intros.
  unfold NotInA.
  intros.
  intuition.
  apply ina_to_in in H.
  destruct H as (v', Hin).
  apply partition_match_key_spec_4 in Hin.
  assumption.
Qed.

Theorem nodupa_unproj:
  forall l,
  NoDupA eq_key (unproj l).
Proof.
  intros.
  functional induction (unproj l).
  - apply NoDupA_cons.
    + intuition.
      apply ina_to_in in H.
      destruct H as (vs', Hin).
      assert (Hx := partition_match_key_spec_5 (k:=k) l').
      assert (Heq : mismatched = snd (partition (match_key k) l')).
      rewrite e2; simpl; auto.
      rewrite <- Heq in Hx.
      destruct vs'.
      * apply unproj_absurd in Hin. inversion Hin.
      * assert (Hinv : In v0 (v0 :: vs')).
        apply in_eq.
        apply in_unproj_to_in with (v:=v0) in Hin.
        unfold NotInA in Hx.
        apply in_to_ina in Hin.
        apply (Hx v0) in Hin.
        inversion Hin.
        assumption.
    + assumption.
  - auto.
Qed.

End MATCH.

Module Project (M:FMapInterface.WS) (S:FSetInterface.WS).
Module S_Props := FSetProperties.Properties S.
Module M_Props := FMapFacts.Properties M.
Module M_Extra := MapUtil M.
Module S_Extra := SetUtil S.

Definition proj_edges (e:(M.E.t * S.t)) :=
  let (k, s) := e in
  List.map (fun v=> (k, v)) (S.elements s).

Definition edges m : list (M.E.t * S.E.t) :=
  List.flat_map proj_edges (M.elements m).

Lemma edges_spec:
  forall k e m,
  (forall k1 k2, M.E.eq k1 k2 -> k1 = k2) ->
  (forall e1 e2, S.E.eq e1 e2 -> e1 = e2) ->
  (List.In (k,e) (edges m) <-> (exists (s:S.t), M.MapsTo k s m  /\ S.In e s)).
Proof.
  intros k e m Heq1 Heq2.
  split.
  - intros.
    unfold edges in *.
    rewrite List.in_flat_map in *.
    unfold proj_edges in *.
    destruct H as ((r', ts), (H1, H2)).
    rewrite List.in_map_iff in H2.
    destruct H2 as (t'', (H2, H3)).
    inversion H2; subst; clear H2.
    apply M_Extra.in_elements_impl_maps_to in H1.
    apply S_Extra.in_iff_in_elements in H3.
    exists ts.
    intuition.
    assumption.
  - intros.
    destruct H as (s, (Hmt, Hin)).
    unfold edges.
    rewrite in_flat_map.
    unfold proj_edges.
    exists (k, s).
    intuition.
    + rewrite <- M_Extra.maps_to_iff_in_elements.
      assumption.
      assumption.
    + rewrite in_map_iff.
      exists e.
      intuition.
      rewrite <- S_Extra.in_iff_in_elements.
      assumption.
      assumption.
Qed.

Notation edge := (M.E.t * S.E.t)%type.

Lemma value_eq_dec:
  (forall e1 e2, S.E.eq e1 e2 <-> e1 = e2) ->
  forall (e1 e2:S.E.t),
  {e1 = e2} + {e1 <> e2}.
Proof.
  intros.
  destruct (S.E.eq_dec e1 e2).
  + left.
    apply H.
    assumption.
  + right.
    intuition.
    apply H in H0.
    contradiction n.
Qed.

Lemma key_eq_dec:
  (forall e1 e2, M.E.eq e1 e2 <-> e1 = e2) ->
  forall (e1 e2:M.E.t),
  {e1 = e2} + {e1 <> e2}.
Proof.
  intros.
  destruct (M.E.eq_dec e1 e2).
  + left.
    apply H.
    assumption.
  + right.
    intuition.
    apply H in H0.
    contradiction n.
Qed.

Definition unproj_0
  (k_eq_subst:(forall e1 e2, M.E.eq e1 e2 <-> e1 = e2))
  (l:list edge) : list (M.E.t * (list S.E.t)) := unproj (key_eq_dec k_eq_subst) l.

Let unproj_0_spec
  (k_eq_subst: forall e1 e2, M.E.eq e1 e2 <-> e1 = e2)
  (v_eq_subst: forall e1 e2, S.E.eq e1 e2 <-> e1 = e2) :
  forall k v l,
  (List.In (k, v) l <-> exists l', List.In (k, l') (unproj_0 k_eq_subst l) /\ In v l').
Proof.
  intros.
  split.
  - intros.
    rewrite unproj_spec with (key_eq_dec:=key_eq_dec k_eq_subst) in H.
    auto.
    apply value_eq_dec.
    apply v_eq_subst.
  - intros.
    rewrite unproj_spec with (key_eq_dec:=key_eq_dec k_eq_subst).
    destruct H as (l', (Hkv, Hin)).
    exists l'.
    intuition.
    apply value_eq_dec; apply v_eq_subst.
Qed.

Lemma nodupa_conv (k_eq_subst:(forall e1 e2, M.E.eq e1 e2 <-> e1 = e2)):
  forall {A:Type} l,
  NoDupA (eq_key (A:= A)) l ->
  NoDupA (M.eq_key (elt:=A)) l.
Proof.
  intros.
  induction l.
  - auto.
  - inversion H.
    subst.
    apply NoDupA_cons.
    + intuition.
      rewrite InA_altdef in *.
      rewrite Exists_exists in *.
      destruct H0 as (s, (Hin, Heq)).
      apply H2.
      exists s.
      intuition.
      unfold M.eq_key in *.
      unfold eq_key.
      apply k_eq_subst.
      assumption.
    + apply IHl.
      assumption.
Qed.

Lemma unproj_0_nodupa
  (k_eq_subst: forall e1 e2, M.E.eq e1 e2 <-> e1 = e2)
  (v_eq_subst: forall e1 e2, S.E.eq e1 e2 <-> e1 = e2):
  forall l,
  NoDupA (M.eq_key (elt:=list S.E.t)) (unproj_0 k_eq_subst l).
Proof.
  intros.
  assert (Hx := nodupa_unproj (key_eq_dec k_eq_subst) (value_eq_dec v_eq_subst) l).
  unfold unproj_0.
  apply nodupa_conv.
  auto.
  auto.
Qed.

Definition unproj_1
  (k_eq_subst:(forall e1 e2, M.E.eq e1 e2 <-> e1 = e2))
  (l:list edge) : list (M.E.t * S.t) := map (fun p => (fst p, S_Props.of_list (snd p))) (unproj_0 k_eq_subst l).

Let s_ina_to_in:
  forall v vs,
  (forall e1 e2, S.E.eq e1 e2 -> e1 = e2) ->
  (InA S.E.eq v vs <-> In v vs).
Proof.
  intros.
  split.
  - intros.
    rewrite InA_altdef in H0.
    rewrite Exists_exists in H0.
    destruct H0 as (x, (Hin, Heq)).
    apply H in Heq.
    subst; assumption.
  - intros.
    rewrite InA_altdef.
    rewrite Exists_exists.
    exists v.
    intuition.
Qed.

Let unproj_1_spec
  (k_eq_subst: forall e1 e2, M.E.eq e1 e2 <-> e1 = e2)
  (v_eq_subst: forall e1 e2, S.E.eq e1 e2 <-> e1 = e2):
  forall k v l,
  (List.In (k, v) l <-> exists s, List.In (k, s) (unproj_1 k_eq_subst l) /\ S.In v s).
Proof.
  intros.
  unfold unproj_1.
  split.
  - intros.
    rewrite unproj_0_spec with (k_eq_subst:=k_eq_subst) in H.
    destruct H as (l', (Hkv, Hin)).
    assert (S.In v (S_Props.of_list l')).
    apply S_Props.of_list_1.
    apply s_ina_to_in.
    apply v_eq_subst.
    assumption.
    exists (S_Props.of_list l').
    intuition.
    apply in_map_iff.
    exists (k, l').
    intuition.
    apply v_eq_subst.
  - intros.
    destruct H as (s, (Hkv, Hin)).
    apply in_map_iff in Hkv.
    destruct Hkv as ((k', l'), (Heq, Hin_l)).
    inversion Heq.
    simpl in *.
    subst.
    clear Heq.
    apply S_Props.of_list_1 in Hin.
    rewrite s_ina_to_in in Hin.
    rewrite unproj_0_spec with (k_eq_subst:=k_eq_subst).
    exists l'.
    intuition.
    auto.
    apply v_eq_subst.
Qed.

Let in_unproj_1_to_in
  (k_eq_subst: forall e1 e2, M.E.eq e1 e2 <-> e1 = e2)
  (v_eq_subst: forall e1 e2, S.E.eq e1 e2 <-> e1 = e2):
  forall v s k l,
  S.In v s ->
  List.In (k, s) (unproj_1 k_eq_subst l) ->
  List.In (k, v) l.
Proof.
  intros.
  assert (exists s, List.In (k, s) (unproj_1 k_eq_subst l) /\ S.In v s).
  exists s.
  intuition.
  apply unproj_1_spec in H1.
  auto.
  auto.
Qed.

Lemma ina_map:
  forall {A:Type} {B:Type} f a l,
  (forall a1 a2, M.eq_key (f a1) (f a2) -> M.eq_key a1 a2) ->
  InA (M.eq_key (elt:=A)) (f a) (map f l) ->
  InA (M.eq_key (elt:=B)) a l.
Proof.
  intros.
  intuition.
  induction l.
  - simpl.
    inversion H0.
  - simpl.
    inversion H0.
    + subst.
      rewrite InA_altdef.
      rewrite Exists_exists.
      exists a0.
      intuition.
    + subst.
      apply InA_cons.
      right.
      apply IHl.
      assumption.
Qed.

Lemma nodupa_map:
  forall {A:Type} {B:Type} (f:(M.E.t * A) -> (M.E.t * B)) l,
  (forall a1 a2, M.eq_key (f a1) (f a2) -> M.eq_key a1 a2) ->
  NoDupA (M.eq_key (elt:=A)) l ->
  NoDupA (M.eq_key (elt:=B)) (map f l).
Proof.
  intros.
  induction l.
  - simpl. auto.
  - simpl.
    inversion H0.
    subst.
    apply NoDupA_cons.
    intuition.
    apply ina_map in H1.
    apply H3.
    assumption.
    assumption.
    apply IHl.
    assumption.
Qed.

Lemma unproj_1_nodupa
  (k_eq_subst: forall e1 e2, M.E.eq e1 e2 <-> e1 = e2)
  (v_eq_subst: forall e1 e2, S.E.eq e1 e2 <-> e1 = e2):
  forall l,
  NoDupA (M.eq_key (elt:=S.t)) (unproj_1 k_eq_subst l).
Proof.
  intros.
  unfold unproj_1.
  assert (Hx:= unproj_0_nodupa k_eq_subst v_eq_subst l).
  remember (unproj_0 k_eq_subst l).
  apply nodupa_map.
  intros.
  destruct a1, a2.
  simpl in H.
  unfold M.eq_key in *.
  simpl in *.
  assumption.
  assumption.
Qed.

Definition unproject
  (k_eq_subst:(forall e1 e2, M.E.eq e1 e2 <-> e1 = e2))
  (l:list edge) : M.t S.t
  := M_Props.of_list (unproj_1 k_eq_subst l).

Let ina_to_in
  (k_eq_subst : forall e1 e2, M.E.eq e1 e2 <-> e1 = e2)
  :
  forall {elt:Type} k v l,
  InA (M.eq_key (elt:=elt)) (k, v) l ->
  exists v', In (k, v') l.
Proof.
  intros.
  rewrite InA_altdef in H.
  rewrite Exists_exists in H.
  destruct H as ((k',v'), (Hin, Heq)).
  unfold eq_key in Heq.
  simpl in Heq; subst.
  exists v'.
  unfold M.eq_key in Heq.
  simpl in Heq.
  apply k_eq_subst in Heq.
  subst.
  auto.
Qed.

Let in_to_ina
  (k_eq_subst : forall e1 e2, M.E.eq e1 e2 <-> e1 = e2)
  :
  forall {elt:Type} k v l,
  In (k, v) l ->
  InA (M.eq_key (elt:=elt)) (k, v) l.
Proof.
  intros.
  rewrite InA_altdef.
  rewrite Exists_exists.
  exists (k, v).
  intuition.
  unfold M.eq_key.
  simpl.
  apply k_eq_subst.
  trivial.
Qed.

Theorem unproject_spec
  (k_eq_subst : forall e1 e2, M.E.eq e1 e2 <-> e1 = e2)
  (v_eq_subst : forall e1 e2, S.E.eq e1 e2 <-> e1 = e2)
  :
  forall k v l,
  (List.In (k, v) l <-> exists s, M.MapsTo k s (unproject k_eq_subst l) /\ S.In v s).
Proof.
  intros.
  unfold unproject.
  split.
  - intros.
    rewrite (unproj_1_spec k_eq_subst v_eq_subst) in H.
    destruct H as (s, (Hkv, Hin)).
    exists s.
    intuition.
    apply M_Extra.in_elements_impl_maps_to.
    apply M_Extra.to_list_of_list.
    auto.
    apply unproj_1_nodupa.
    auto.
    auto.
  - intros.
    destruct H as (s, (Hmt, Hin)).
    apply M_Props.of_list_1 in Hmt.
    apply in_unproj_1_to_in with (k_eq_subst:=k_eq_subst) (s:=s); repeat auto.
    rewrite InA_altdef in Hmt.
    rewrite Exists_exists in Hmt.
    destruct Hmt as ((k',s'), (Hin', Heq)).
    unfold M.eq_key_elt in Heq.
    destruct Heq as (Heq1, Heq2).
    simpl in *.
    apply k_eq_subst in Heq1.
    subst.
    intuition.
    apply unproj_1_nodupa.
    auto.
Qed.
End Project.