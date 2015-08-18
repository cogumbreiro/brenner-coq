#!/bin/bash
version=8.4
coq_shell_url="https://raw.githubusercontent.com/gares/opam-coq-shell/master/src/opam-coq"
curl -s "${coq_shell_url}" | bash /dev/stdin init $version && # Install Coq dependencies
eval `opam config env --switch=coq-shell-$version` &&
coq_makefile -f _CoqProject -o Makefile &&
opam install coq:aniceto || (echo "Install https://bitbucket.org/cogumbreiro/aniceto-coq first."; exit 1)
