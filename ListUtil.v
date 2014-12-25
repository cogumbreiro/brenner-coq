Require Import Lists.ListSet.
Require Import Lists.List.
Require Import Program.Wf.
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

Program Fixpoint repeat_filter (l:list A) {measure (length l)} :=
  let l' := filter f l in
  if list_eq_dec eq_dec l l' then l
  else repeat_filter l'.
Next Obligation.
  destruct (filter_inv l).
  - contradiction H.
  - assumption.
Qed.

End LISTS.

Implicit Arguments filter_inv.

Section FEEDBACK.
Variable A:Type.
Variable eq_dec : forall (v1 v2:A), {v1 = v2} + {v1 <> v2}.
Variable f : list A -> A -> bool.

Program Fixpoint feedback_filter (l:list A) {measure (length l)} :=
  let l' := filter (f l) l in
  if list_eq_dec eq_dec l l' then l
  else feedback_filter l'.
Next Obligation.
Proof.
  destruct (filter_inv (f l) l).
  - contradiction H.
  - auto.
Qed.
End FEEDBACK.
