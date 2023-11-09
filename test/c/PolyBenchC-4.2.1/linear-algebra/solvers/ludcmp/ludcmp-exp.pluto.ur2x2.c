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
/* ludcmp.c: this file is part of PolyBench/C */

#include <stdio.h>
#include <unistd.h>
#include <string.h>
#include <math.h>

/* Include polybench common header. */
#include <polybench.h>

/* Include benchmark-specific header. */
#include "ludcmp.h"


/* Array initialization. */
static
void init_array (int n,
		 DATA_TYPE POLYBENCH_2D(A,N,N,n,n),
		 DATA_TYPE POLYBENCH_1D(b,N,n),
		 DATA_TYPE POLYBENCH_1D(x,N,n),
		 DATA_TYPE POLYBENCH_1D(y,N,n))
{
  int i, j;
  DATA_TYPE fn = (DATA_TYPE)n;

  for (i = 0; i < n; i++)
    {
      x[i] = 0;
      y[i] = 0;
      b[i] = (i+1)/fn/2.0 + 4;
    }

  for (i = 0; i < n; i++)
    {
      for (j = 0; j <= i; j++)
	A[i][j] = (DATA_TYPE)(-j % n) / n + 1;
      for (j = i+1; j < n; j++) {
	A[i][j] = 0;
      }
      A[i][i] = 1;
    }

  /* Make the matrix positive semi-definite. */
  /* not necessary for LU, but using same code as cholesky */
  int r,s,t;
  POLYBENCH_2D_ARRAY_DECL(B, DATA_TYPE, N, N, n, n);
  for (r = 0; r < n; ++r)
    for (s = 0; s < n; ++s)
      (POLYBENCH_ARRAY(B))[r][s] = 0;
  for (t = 0; t < n; ++t)
    for (r = 0; r < n; ++r)
      for (s = 0; s < n; ++s)
	(POLYBENCH_ARRAY(B))[r][s] += A[r][t] * A[s][t];
    for (r = 0; r < n; ++r)
      for (s = 0; s < n; ++s)
	A[r][s] = (POLYBENCH_ARRAY(B))[r][s];
  POLYBENCH_FREE_ARRAY(B);

}


/* DCE code. Must scan the entire live-out data.
   Can be used also to check the correctness of the output. */
static
void print_array(int n,
		 DATA_TYPE POLYBENCH_1D(x,N,n))

{
  int i;

  POLYBENCH_DUMP_START;
  POLYBENCH_DUMP_BEGIN("x");
  for (i = 0; i < n; i++) {
    if (i % 20 == 0) fprintf (POLYBENCH_DUMP_TARGET, "\n");
    fprintf (POLYBENCH_DUMP_TARGET, DATA_PRINTF_MODIFIER, x[i]);
  }
  POLYBENCH_DUMP_END("x");
  POLYBENCH_DUMP_FINISH;
}


/* Main computational kernel. The whole function will be timed,
   including the call and return. */
static
void kernel_ludcmp(int n,
		   DATA_TYPE POLYBENCH_2D(A,N,N,n,n),
		   DATA_TYPE POLYBENCH_1D(b,N,n),
		   DATA_TYPE POLYBENCH_1D(x,N,n),
		   DATA_TYPE POLYBENCH_1D(y,N,n))
{
  int i, j, k;

  DATA_TYPE POLYBENCH_1D(w1,N,n);
  DATA_TYPE POLYBENCH_2D(w2,N,N,n,n);

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
  int t1, t2, t3, t4, t5, t6, t7, t8, t9, t10;
 register int lbv, ubv;
/* Start of CLooG code */
if (_PB_N >= 1) {
  for (t2=0;t2<=_PB_N-1;t2++) {
    if (t2 >= 1) {
      w2[t2][0] = A[t2][0];;
      A[t2][0] = w2[t2][0] / A[0][0];;
    }
    for (t4=1;t4<=t2-1;t4++) {
      w2[t2][t4] = A[t2][t4];;
      DATA_TYPE __r0 = w2[t2][t4];
      int __up1 = t4-1;
      for (t6=0;t6<=__up1-3;t6+=4) {
        __r0 -= A[t2][t6] * A[t6][t4];;
        __r0 -= A[t2][(t6+1)] * A[(t6+1)][t4];;
        __r0 -= A[t2][(t6+2)] * A[(t6+2)][t4];;
        __r0 -= A[t2][(t6+3)] * A[(t6+3)][t4];;
      }
      for (;t6<=__up1;t6++) {
        __r0 -= A[t2][t6] * A[t6][t4];;
      }
      w2[t2][t4] = __r0;
      A[t2][t4] = w2[t2][t4] / A[t4][t4];;
    }
    for (t4=ceild(t2-31,32);t4<=floord(_PB_N-1,32);t4++) {
      for (t7=max(t2,32*t4);t7<=min(_PB_N-1,32*t4+31);t7++) {
        w2[t2][t7] = A[t2][t7];;
      }
      for (t6=0;t6<=floord(t2-1,32);t6++) {
        int __up2 = min(_PB_N-1,32*t4+31);
        for (t7=max(t2,32*t4);t7<=__up2-1;t7+=2) {
          DATA_TYPE __r0 = w2[t2][t7];
          DATA_TYPE __r1 = w2[t2][(t7+1)];
          int __up3 = min(t2-1,32*t6+31);
          for (t9=32*t6;t9<=__up3-1;t9+=2) {
            __r0 -= A[t2][t9] * A[t9][t7];;
            __r0 -= A[t2][(t9+1)] * A[(t9+1)][t7];;
            __r1 -= A[t2][t9] * A[t9][(t7+1)];;
            __r1 -= A[t2][(t9+1)] * A[(t9+1)][(t7+1)];;
          }
          for (;t9<=__up3;t9++) {
            __r0 -= A[t2][t9] * A[t9][t7];;
            __r1 -= A[t2][t9] * A[t9][(t7+1)];;
          }
          w2[t2][t7] = __r0;
          w2[t2][(t7+1)] = __r1;
        }
        for (;t7<=__up2;t7++) {
          DATA_TYPE __r0 = w2[t2][t7];
          int __up4 = min(t2-1,32*t6+31);
          for (t9=32*t6;t9<=__up4-1;t9+=2) {
            __r0 -= A[t2][t9] * A[t9][t7];;
            __r0 -= A[t2][(t9+1)] * A[(t9+1)][t7];;
          }
          for (;t9<=__up4;t9++) {
            __r0 -= A[t2][t9] * A[t9][t7];;
          }
          w2[t2][t7] = __r0;
        }
      }
      for (t7=max(t2,32*t4);t7<=min(_PB_N-1,32*t4+31);t7++) {
        A[t2][t7] = w2[t2][t7];;
      }
    }
  }
  w1[0] = b[0];;
  y[0] = w1[0];;
  for (t2=1;t2<=_PB_N-1;t2++) {
    w1[t2] = b[t2];;
    for (t4=0;t4<=t2-1;t4++) {
      w1[t2] -= A[t2][t4] * y[t4];;
    }
    y[t2] = w1[t2];;
  }
  w1[(_PB_N-1)] = y[(_PB_N-1)];;
  x[(_PB_N-1)] = w1[(_PB_N-1)] / A[(_PB_N-1)][(_PB_N-1)];;
  for (t2=-_PB_N+2;t2<=0;t2++) {
    w1[-t2] = y[-t2];;
    for (t4=-t2+1;t4<=_PB_N-1;t4++) {
      w1[-t2] -= A[-t2][t4] * x[t4];;
    }
    x[-t2] = w1[-t2] / A[-t2][-t2];;
  }
}
/* End of CLooG code */

}


int main(int argc, char** argv)
{
  /* Retrieve problem size. */
  int n = N;

  /* Variable declaration/allocation. */
  POLYBENCH_2D_ARRAY_DECL(A, DATA_TYPE, N, N, n, n);
  POLYBENCH_1D_ARRAY_DECL(b, DATA_TYPE, N, n);
  POLYBENCH_1D_ARRAY_DECL(x, DATA_TYPE, N, n);
  POLYBENCH_1D_ARRAY_DECL(y, DATA_TYPE, N, n);


  /* Initialize array(s). */
  init_array (n,
	      POLYBENCH_ARRAY(A),
	      POLYBENCH_ARRAY(b),
	      POLYBENCH_ARRAY(x),
	      POLYBENCH_ARRAY(y));

  /* Start timer. */
  polybench_start_instruments;

  /* Run kernel. */
  kernel_ludcmp (n,
		 POLYBENCH_ARRAY(A),
		 POLYBENCH_ARRAY(b),
		 POLYBENCH_ARRAY(x),
		 POLYBENCH_ARRAY(y));

  /* Stop and print timer. */
  polybench_stop_instruments;
  polybench_print_instruments;

  /* Prevent dead-code elimination. All live-out data must be printed
     by the function call in argument. */
  polybench_prevent_dce(print_array(n, POLYBENCH_ARRAY(x)));

  /* Be clean. */
  POLYBENCH_FREE_ARRAY(A);
  POLYBENCH_FREE_ARRAY(b);
  POLYBENCH_FREE_ARRAY(x);
  POLYBENCH_FREE_ARRAY(y);

  return 0;
}

