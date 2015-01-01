Require Import Lists.ListSet.
Require Import Lists.List.
Require Import Bool.

Require Import Recdef. (* Required by Function *)
Require Import Coq.Arith.Wf_nat. (* Required implicitly by measure obligations *)

Section LISTS.

Variable A:Type.
Variable eq_dec : forall (v1 v2:A), {v1 = v2} + {v1 <> v2}.
Variable f : A -> bool.

Lemma filter_length:
  forall l,
  length (filter f l) <= length l.
Proof.
  intros.
  induction l.
  - auto.
  - simpl.
    destruct (f a).
    + simpl.
      auto with *.
    + auto with *.
Qed.

Lemma filter_inv:
  forall l,
  {l = filter f l} + {length l > length (filter f l)}.
Proof.
  intros.
  induction l.
  - left.
    auto.
  - destruct IHl.
    + simpl.
      rewrite <- e in *; clear e.
      destruct (f a).
      * left.
        auto.
      * right.
        auto with *.
    + simpl.
      destruct (f a);(
        right;
        simpl;
        auto with *
      ).
Qed.

Lemma filter_incl:
  forall l,
  incl (filter f l) l.
Proof.
  intros.
  unfold incl.
  intros.
  rewrite filter_In in H.
  intuition.
Qed.

Lemma filter_refl:
  forall l,
  filter f l = l ->
  incl l (filter f l).
Proof.
  intros.
  induction l.
  - simpl.
    unfold incl.
    intros.
    inversion H0.
  - simpl in *.
    destruct (f a); (
      rewrite H;
      apply incl_refl).
Qed.

Lemma filter_forallb:
  forall l,
  filter f l = l <->
  forallb f l = true.
Proof.
  intros.
  split.
  - intros.
    induction l.
    + auto.
    + assert (Hfa : f a = true).
      assert (Ha : In a (filter f (a :: l))).
      rewrite H.
      apply in_eq.
      rewrite filter_In in Ha.
      intuition.
      simpl in *.
      destruct (f a).
      * inversion H.
        rewrite H1.
        auto.
      * inversion Hfa. (*absurd *)
  - intros. induction l.
    auto.
    simpl in *.
    rewrite Bool.andb_true_iff in H.
    destruct H as (Hl, Hr).
    apply IHl in Hr.
    destruct (f a).
    + rewrite Hr. trivial.
    + inversion Hl.
Qed.

Lemma existsb_inv:
  forall {B:Type} (a:B) l g,
  existsb g (a :: l) = true ->
  g a = false ->
  existsb g l = true.
Proof.
  intros.
  simpl in H.
  rewrite H0 in H.
  auto.
Qed.

Lemma forallb_existsb:
  forall l,
  forallb f l = negb (existsb (fun x => negb (f x)) l).
Proof.
  intros.
  induction l.
  - auto.
  - simpl.
    rewrite negb_orb.
    rewrite negb_involutive.
    rewrite <- IHl.
    auto.
Qed.
(*
Lemma forallb_existsb:
  forall l,
  forallb f l = false <->
  existsb (fun x => negb (f x)) l = true.
Proof.
  intros.
  split.
  * intros.
  induction l.
  - inversion H.
  - simpl in H.
    remember (f a) as fa.
    destruct fa.
    + simpl in *.
      apply IHl in H.
      intuition.
    + rewrite existsb_exists.
      exists a.
      intuition.
      rewrite <- Heqfa.
      auto.
  * intros.
    induction l.
    - inversion H.
    - simpl.
      remember (f a) as fa.
      destruct fa.
      apply existsb_inv in H.
      apply IHl.
      assumption.
      rewrite <- Heqfa.
      auto.
      auto.
Qed.*)

Lemma Forall_forallb:
  forall l,
  Forall (fun x => Is_true (f x)) l <->
  forallb f l = true.
Proof.
  split.
  + intro.
    rewrite forallb_forall.
    intros.
    rewrite Forall_forall in H.
    apply H in H0.
    apply Is_true_eq_true in H0.
    trivial.
  + intros.
    rewrite forallb_forall in H.
    rewrite Forall_forall.
    intros.
    apply Is_true_eq_left.
    apply H.
    assumption.
Qed.

End LISTS.

Implicit Arguments filter_inv.

Section FEEDBACK.
Variable A:Type.
Variable eq_dec : forall (v1 v2:A), {v1 = v2} + {v1 <> v2}.
Variable f : list A -> A -> bool.

Function feedback_filter (l:list A) {measure length l} :=
  let fl := filter (f l) l in
  if list_eq_dec eq_dec l fl then l 
  else feedback_filter fl.
Proof.
  intros.
  destruct (filter_inv (f l) l).
  - contradiction anonymous.
  - auto.
Defined.

Lemma feedback_filter_incl:
  forall l,
  incl (feedback_filter l) l.
Proof.
  intros.
  elim l using feedback_filter_rec.
  - intros.
    apply incl_refl.
  - intros. clear l. rename l0 into l.
    remember (filter (f l) l) as l'.
    assert (Hx : incl l' l).
    rewrite Heql'.
    apply filter_incl.
    apply incl_tran with (m:=l'); repeat auto.
Qed.

Lemma feedback_filter_simpl:
  forall l,
  filter (f l) l = l ->
  feedback_filter l = l.
Proof.
  intros.
  rewrite feedback_filter_equation.
  destruct (list_eq_dec eq_dec l (filter (f l) l)).
  - auto.
  - contradiction n.
    auto.
Qed.

Let if_list_eq_dec_eq:
  forall {B:Type} l (a b:B),
  (if list_eq_dec eq_dec l l then a else b) = a.
Proof.
  intros.
  destruct (list_eq_dec eq_dec l l).
  - auto.
  - contradiction n.
    auto.
Qed.

Let if_list_eq_filter_forallb:
  forall {B:Type} l (a b:B),
  (if list_eq_dec eq_dec l (filter (f l) l) then a else b)
  = (if forallb (f l) l then a else b).
Proof.
  intros.
  remember (filter (f l) l) as fl.
  symmetry in Heqfl.
  remember (forallb (f l) l) as flb.
  symmetry in Heqflb.
  destruct flb.
  - rewrite <- filter_forallb in Heqflb.
    rewrite Heqfl in Heqflb.
    rewrite Heqflb.
    apply if_list_eq_dec_eq.
  - destruct (list_eq_dec eq_dec l fl).
    + rewrite <- e in Heqfl.
      rewrite filter_forallb in Heqfl.
      rewrite Heqfl in Heqflb.
      inversion Heqflb.
    + auto.
Qed.

Let feedback_filter_equation2:
  forall l : list A,
  feedback_filter l =
  (if forallb (f l) l
  then l
  else feedback_filter (filter (f l) l)).
Proof.
  intros.
  rewrite feedback_filter_equation.
  rewrite if_list_eq_filter_forallb.
  auto.
Qed.

Lemma feedback_filter_prop:
  forall l fl,
  feedback_filter l = fl <->
  (Forall (fun x=>Is_true (f l x)) l /\ fl = l)
  \/
  (exists x, In x l /\ Is_true (negb (f l x)) /\ fl = feedback_filter (filter (f l) l)).
Proof.
  intros.
  split.
  - intros.
    rewrite feedback_filter_equation2 in H.
    remember (forallb (f l) l) as flb.
    symmetry in Heqflb.
    destruct flb.
    + rewrite forallb_forall in Heqflb.
      left.
      rewrite Forall_forall.
      intuition.
      apply Is_true_eq_left.
      apply Heqflb in H0.
      assumption.
    + right.
      rewrite forallb_existsb in Heqflb.
      rewrite negb_false_iff in Heqflb.
      rewrite existsb_exists in Heqflb.
      destruct Heqflb as (x, (x_in, flx)).
      exists x.
      apply Is_true_eq_left in flx.
      intuition.
   - intros.
     rewrite feedback_filter_equation2.
     destruct H as [(H1,H2)|(x, (H1, (H2, H3)))].
     + apply Forall_forallb in H1.
       rewrite H1.
       auto.
     + rewrite <- H3.
       remember (forallb (f l) l) as c.
       symmetry in Heqc.
       destruct c.
       * rewrite forallb_forall in Heqc.
         apply Heqc in H1.
         apply Is_true_eq_true in H2.
         rewrite negb_true_iff in H2.
         rewrite H1 in H2.
         inversion H2.
       * auto.
Qed.

Lemma feedback_filter_in:
  forall x l,
  In x (feedback_filter l) -> f (feedback_filter l) x = true.
Proof.
  intros.
  functional induction (feedback_filter l).
  - assert (Hf := _x).
    symmetry in Hf.
    rewrite filter_forallb in Hf.
    rewrite forallb_forall in Hf.
    apply Hf in H.
    assumption.
  - apply IHl0. auto.
Qed.

End FEEDBACK.

Implicit Arguments feedback_filter.
Implicit Arguments feedback_filter_equation.
