Require Import
  Graph
  Bipartite.
Require OGraph.

Record Bipartite := mk_bipartite {
  vertex_a : Type;
  vertex_b : Type;
  AB : vertex_a -> vertex_b -> Prop;
  BA : vertex_b -> vertex_a -> Prop
}.

Definition AA (bp:Bipartite) := AA (vertex_a bp) (vertex_b bp) (AB bp) (BA bp).
Definition BB (bp:Bipartite) := BB (vertex_a bp) (vertex_b bp) (AB bp) (BA bp).

Definition contract_a (bp:Bipartite) := OGraph.mk_digraph (vertex_a bp) (AA bp).
Definition contract_b (bp:Bipartite) := OGraph.mk_digraph (vertex_b bp) (BB bp).

Definition ACycle (bp:Bipartite) := OGraph.Cycle (contract_a bp).
Definition BCycle (bp:Bipartite) := OGraph.Cycle (contract_b bp).
(*
Definition ACycle (bp:Bipartite) := Cycle (vertex_a bp) (AA bp).
Definition BCycle (bp:Bipartite) := Cycle (vertex_b bp) (BB bp).
*)
Definition cycle_a_to_cycle_b := fun (bp:Bipartite) =>
  cycle_a_to_b
    (vertex_a bp) 
    (vertex_b bp)
    (AB bp)
    (BA bp).

Let cycle_b_to_cycle_a' := fun (bp:Bipartite) =>
  cycle_a_to_b
    (vertex_b bp)
    (vertex_a bp)
    (BA bp)
    (AB bp).

Lemma cycle_b_to_cycle_a :
  forall (bp : Bipartite) (w : list (vertex_b bp * vertex_b bp)),
       Cycle (vertex_b bp)
         (Bipartite.BB (vertex_a bp) (vertex_b bp) (AB bp) (BA bp)) w ->
       exists w' : list (vertex_a bp * vertex_a bp),
         Cycle (vertex_a bp)
           (Bipartite.AA (vertex_a bp) (vertex_b bp) (AB bp) (BA bp)) w'.
Proof.
  intros.
  rewrite cycle_b_aa_eq_bb in H.
  assert (H':= cycle_b_to_cycle_a' bp w H).
  destruct H' as (w', H').
  exists w'.
  rewrite cycle_b_aa_eq_bb in H'.
  assumption.
Qed.
