#!/bin/sh

gcc -O3 -I utilities utilities/polybench.c -DPOLYBENCH_TIME -DPOLYBENCH_DUMP_ARRAYS $* -lm
