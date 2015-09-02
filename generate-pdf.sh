#!/bin/sh
make all
make COQDOCFLAGS="-g -l" all.pdf
