#include <math.h>
#define ceild(n,d)  ceil(((double)(n))/((double)(d)))
#define floord(n,d) floor(((double)(n))/((double)(d)))
#define max(x,y)    ((x) > (y)? (x) : (y))
#define min(x,y)    ((x) < (y)? (x) : (y))

/**
 * This version is stamped on May 10, 2016
 *
 * Contact:
 *   Louis-Noel Pouchet <pouchet.ohio-state.edu>
 *   Tomofumi Yuki <tomofumi.yuki.fr>
 *
 * Web address: http://polybench.sourceforge.net
 */
/* trmm.c: this file is part of PolyBench/C */

#include <stdio.h>
#include <unistd.h>
#include <string.h>
#include <math.h>

/* Include polybench common header. */
#include <polybench.h>

/* Include benchmark-specific header. */
#include "trmm.h"


/* Array initialization. */
static
void init_array(int m, int n,
		DATA_TYPE *alpha,
		DATA_TYPE POLYBENCH_2D(A,M,M,m,m),
		DATA_TYPE POLYBENCH_2D(B,M,N,m,n))
{
  int i, j;

  *alpha = 1.5;
  for (i = 0; i < m; i++) {
    for (j = 0; j < i; j++) {
      A[i][j] = (DATA_TYPE)((i+j) % m)/m;
    }
    A[i][i] = 1.0;
    for (j = 0; j < n; j++) {
      B[i][j] = (DATA_TYPE)((n+(i-j)) % n)/n;
    }
 }

}


/* DCE code. Must scan the entire live-out data.
   Can be used also to check the correctness of the output. */
static
void print_array(int m, int n,
		 DATA_TYPE POLYBENCH_2D(B,M,N,m,n))
{
  int i, j;

  POLYBENCH_DUMP_START;
  POLYBENCH_DUMP_BEGIN("B");
  for (i = 0; i < m; i++)
    for (j = 0; j < n; j++) {
	if ((i * m + j) % 20 == 0) fprintf (POLYBENCH_DUMP_TARGET, "\n");
	fprintf (POLYBENCH_DUMP_TARGET, DATA_PRINTF_MODIFIER, B[i][j]);
    }
  POLYBENCH_DUMP_END("B");
  POLYBENCH_DUMP_FINISH;
}


/* Main computational kernel. The whole function will be timed,
   including the call and return. */
static
void kernel_trmm(int m, int n,
		 DATA_TYPE alpha,
		 DATA_TYPE POLYBENCH_2D(A,M,M,m,m),
		 DATA_TYPE POLYBENCH_2D(B,M,N,m,n))
{
  int i, j, k;

//BLAS parameters
//SIDE   = 'L'
//UPLO   = 'L'
//TRANSA = 'T'
//DIAG   = 'U'
// => Form  B := alpha*A**T*B.
// A is MxM
// B is MxN
/* Copyright (C) 1991-2018 Free Software Foundation, Inc.
   This file is part of the GNU C Library.

   The GNU C Library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   The GNU C Library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with the GNU C Library; if not, see
   <http://www.gnu.org/licenses/>.  */
/* This header is separate from features.h so that the compiler can
   include it implicitly at the start of every compilation.  It must
   not itself include <features.h> or any other header that includes
   <features.h> because the implicit include comes before any feature
   test macros that may be defined in a source file before it first
   explicitly includes a system header.  GCC knows the name of this
   header in order to preinclude it.  */
/* glibc's intent is to support the IEC 559 math functionality, real
   and complex.  If the GCC (4.9 and later) predefined macros
   specifying compiler intent are available, use them to determine
   whether the overall intent is to support these features; otherwise,
   presume an older compiler has intent to support these features and
   define these macros by default.  */
/* wchar_t uses Unicode 10.0.0.  Version 10.0 of the Unicode Standard is
   synchronized with ISO/IEC 10646:2017, fifth edition, plus
   the following additions from Amendment 1 to the fifth edition:
   - 56 emoji characters
   - 285 hentaigana
   - 3 additional Zanabazar Square characters */
/* We do not support C11 <threads.h>.  */
  int t1, t2, t3, t4, t5, t6, t7;
 register int lbv, ubv;
/* Start of CLooG code */
if ((_PB_M >= 1) && (_PB_N >= 1)) {
  if (_PB_M >= 2) {
    for (t2=0;t2<=floord(_PB_N-1,32);t2++) {
      for (t3=0;t3<=floord(_PB_M-1,32);t3++) {
        for (t4=0;t4<=min(floord(_PB_M-2,32),t3);t4++) {
          for (t5=max(32*t3,32*t4+1);t5<=min(_PB_M-1,32*t3+31)-1;t5+=2) {
            int __up1 = min(32*t4+31,t5-1);
            for (t6=32*t4;t6<=__up1-1;t6+=2) {
              DATA_TYPE __r0 = A[t5][t6];
              DATA_TYPE __r1 = A[t5][(t6+1)];
              DATA_TYPE __r2 = A[(t5+1)][t6];
              DATA_TYPE __r3 = A[(t5+1)][(t6+1)];
              for (t7=32*t2;t7<=min(_PB_N-1,32*t2+31);t7++) {
                B[t6][t7] += __r0 * B[t5][t7];;
                B[(t6+1)][t7] += __r1 * B[t5][t7];;
                B[t6][t7] += __r2 * B[(t5+1)][t7];;
                B[(t6+1)][t7] += __r3 * B[(t5+1)][t7];;
              }
            }
            for (;t6<=__up1;t6++) {
              DATA_TYPE __r0 = A[t5][t6];
              DATA_TYPE __r2 = A[(t5+1)][t6];
              for (t7=32*t2;t7<=min(_PB_N-1,32*t2+31);t7++) {
                B[t6][t7] += __r0 * B[t5][t7];;
                B[t6][t7] += __r2 * B[(t5+1)][t7];;
              }
            }
            if (t5<=32*t4+31) {
              t6=t5;
              for (t7=32*t2;t7<=min(_PB_N-1,32*t2+31);t7++) {
                B[t6][t7] += A[(t5+1)][t6] * B[(t5+1)][t7];;
              }
            }
          }
          for (;t5<=min(_PB_M-1,32*t3+31);t5++) {
            int __up2 = min(32*t4+31,t5-1);
            for (t6=32*t4;t6<=__up2-1;t6+=2) {
              DATA_TYPE __r0 = A[t5][t6];
              DATA_TYPE __r1 = A[t5][(t6+1)];
              for (t7=32*t2;t7<=min(_PB_N-1,32*t2+31);t7++) {
                B[t6][t7] += __r0 * B[t5][t7];;
                B[(t6+1)][t7] += __r1 * B[t5][t7];;
              }
            }
            for (;t6<=__up2;t6++) {
              DATA_TYPE __r0 = A[t5][t6];
              for (t7=32*t2;t7<=min(_PB_N-1,32*t2+31);t7++) {
                B[t6][t7] += __r0 * B[t5][t7];;
              }
            }
          }
        }
      }
    }
  }
  for (t2=0;t2<=floord(_PB_M-1,32);t2++) {
    for (t3=0;t3<=floord(_PB_N-1,32);t3++) {
      for (t4=32*t2;t4<=min(_PB_M-1,32*t2+31);t4++) {
        for (t5=32*t3;t5<=min(_PB_N-1,32*t3+31);t5++) {
          B[t4][t5] = alpha * B[t4][t5];;
        }
      }
    }
  }
}
/* End of CLooG code */

}


int main(int argc, char** argv)
{
  /* Retrieve problem size. */
  int m = M;
  int n = N;

  /* Variable declaration/allocation. */
  DATA_TYPE alpha;
  POLYBENCH_2D_ARRAY_DECL(A,DATA_TYPE,M,M,m,m);
  POLYBENCH_2D_ARRAY_DECL(B,DATA_TYPE,M,N,m,n);

  /* Initialize array(s). */
  init_array (m, n, &alpha, POLYBENCH_ARRAY(A), POLYBENCH_ARRAY(B));

  /* Start timer. */
  polybench_start_instruments;

  /* Run kernel. */
  kernel_trmm (m, n, alpha, POLYBENCH_ARRAY(A), POLYBENCH_ARRAY(B));

  /* Stop and print timer. */
  polybench_stop_instruments;
  polybench_print_instruments;

  /* Prevent dead-code elimination. All live-out data must be printed
     by the function call in argument. */
  polybench_prevent_dce(print_array(m, n, POLYBENCH_ARRAY(B)));

  /* Be clean. */
  POLYBENCH_FREE_ARRAY(A);
  POLYBENCH_FREE_ARRAY(B);

  return 0;
}

