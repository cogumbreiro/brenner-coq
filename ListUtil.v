Require Import Lists.ListSet.

Section LISTS.

Variable A:Type.
Variable eq_dec : forall (v1 v2:A), {v1 = v2} + {v1 <> v2}.
(*
Definition set_leb 
  (s1 s2:set A): bool :=
  match set_diff eq_dec s1 s2 with
    | nil => true
    | cons _ _ => false
  end.

Definition set_le
  (s1 s2:list A) :=
  forall x, set_In x s1 -> set_In x s2.

Lemma set_le_in:
  forall (x:A) s1 s2,
  List.In x s1 ->
  set_le s1 s2 ->
  List.In x s2.
Proof.
  intros.
  unfold set_le in *.
  assert (x_in := H0 x).
  unfold set_In in *.
  apply x_in in H.
  assumption.
Qed.
*)
End LISTS.

(*Implicit Arguments set_le.*)