#!/bin/bash
USER="$1"
[[ -z $USER ]] && USER=cogumbreiro
git push &&
(git push --mirror git@bitbucket.org:$USER/brenner-coq.git;
git push --mirror git@github.com:$USER/brenner-coq.git)

