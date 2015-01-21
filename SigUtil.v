Notation "'Sig_no'" := (False_rec _ _) (at level 42).
Notation "'Sig_yes' e" := (exist _ e _) (at level 42).
Notation "'Sig_take' e" :=
  (match e with Sig_yes ex => ex end) (at level 42).
