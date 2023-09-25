#!/bin/sh

echo 'Compile base'
gcc -O3 -I utilities -I linear-algebra/kernels/atax utilities/polybench.c linear-algebra/blas/gemm/gemm.c -o gemm.base

echo 'Compile pluto'
gcc -O3 -I utilities -I linear-algebra/kernels/atax utilities/polybench.c linear-algebra/blas/gemm/gemm.pluto.c -o gemm.pluto
