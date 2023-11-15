#!/bin/sh

echo 'Compile base'
gcc -O3 -I utilities -I linear-algebra/blas/gemm utilities/polybench.c linear-algebra/blas/gemm/gemm.c -o gemm.base

echo 'Compile pluto'
gcc -O3 -I utilities -I linear-algebra/blas/gemm utilities/polybench.c linear-algebra/blas/gemm/gemm.pluto.c -o gemm.pluto -lm

echo 'Compile pluto unroll-and-jam (factor: i=2, j=2, k=1)'
gcc -O3 -I utilities -I linear-algebra/blas/gemm utilities/polybench.c linear-algebra/blas/gemm/gemm.pluto.ur2x2x1.c -o gemm.pluto.ur2x2x1 -lm
