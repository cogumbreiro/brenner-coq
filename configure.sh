#!/bin/bash
check_pkg() {
    opam search $@ > /dev/null
}

install_coq() {
  echo "Installing Coq over OPAM..."
  opam repo add coq-released https://coq.inria.fr/opam/released &&
  (opam install coq || true)
}

install_aniceto() {
  if (echo -e "Require Aniceto.List.\n" | coqtop 2>&1 | grep Error); then
    echo "Installing Aniceto..." &&
    opam pin add --dev-repo coq-aniceto https://gitlab.com/cogumbreiro/aniceto-coq.git
  fi
}
coq_shell_url="https://raw.githubusercontent.com/gares/opam-coq-shell/master/src/opam-coq"
(check_pkg coq || install_coq) &&
(check_pkg coq-aniceto || install_aniceto) &&
(test -f Makefile || coq_makefile -f _CoqProject -o Makefile)

