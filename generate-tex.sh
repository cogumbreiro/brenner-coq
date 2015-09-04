#!/bin/sh
make all
make COQDOCFLAGS="--body-only -g -l" "$@"
