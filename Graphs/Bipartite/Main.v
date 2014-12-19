Require
  Graphs.Core
  Graphs.Bipartite.Core.
Require Graphs.Main.

Module G := Graphs.Core.
Module I := Graphs.Main.
Module B := Graphs.Bipartite.Core.

Record Bipartite := mk_bipartite {
  vertex_a : Type;
  vertex_b : Type;
  AB : vertex_a -> vertex_b -> Prop;
  BA : vertex_b -> vertex_a -> Prop
}.

Notation b_edge bp := (vertex_b bp * vertex_b bp) % type.
Notation a_edge bp := (vertex_a bp * vertex_a bp) % type.

Notation b_walk bp := (list (b_edge bp)).
Notation a_walk bp := (list (a_edge bp)).
Notation AA bp := (B.AA (AB bp) (BA bp)).
Notation BB bp := (B.BB (AB bp) (BA bp)).

Notation AWalk bp := (G.Walk (AA bp)).
Notation BWalk bp := (G.Walk (BB bp)).

Notation ABA bp := (B.ABA (AB bp) (BA bp)).
Notation BAB bp := (B.BAB (AB bp) (BA bp)).

Notation contract_a bp := (I.mk_digraph (vertex_a bp) (AA bp)).
Notation contract_b bp := (I.mk_digraph (vertex_b bp) (BB bp)).

Notation ACycle bp := (I.Cycle (contract_a bp)).
Notation BCycle bp := (I.Cycle (contract_b bp)).
