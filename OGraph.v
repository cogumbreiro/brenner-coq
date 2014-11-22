Require Graph.

Record Digraph := mk_digraph {
  vertex : Type;
  Edge : (vertex*vertex)%type -> Prop
}.

Definition edge (d:Digraph) := ((vertex d) * (vertex d))%type.
Definition walk (d:Digraph) := (list (edge d)).
Definition Walk (d:Digraph) := (Graph.Walk (vertex d) (Edge d)).
Definition Cycle (d:Digraph) := (Graph.Cycle (vertex d) (Edge d)).
Definition cycle_def (d:Digraph) := Graph.cycle_def (vertex d) (Edge d).
Definition End (d:Digraph) := Graph.End (vertex d).
