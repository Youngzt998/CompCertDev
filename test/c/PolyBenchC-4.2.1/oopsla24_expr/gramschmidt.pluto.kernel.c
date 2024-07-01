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
/* gramschmidt.c: this file is part of PolyBench/C */

#include <stdio.h>
#include <unistd.h>
#include <string.h>
#include <math.h>

/* Include polybench common header. */
#include <polybench.h>

/* Include benchmark-specific header. */
#include "gramschmidt.h"


void kernel_gramschmidt(int m, int n,
			DATA_TYPE POLYBENCH_2D(A,M,N,m,n),
			DATA_TYPE POLYBENCH_2D(R,N,N,n,n),
			DATA_TYPE POLYBENCH_2D(Q,M,N,m,n))
{
  int i, j, k;

  DATA_TYPE nrm;

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
  int t1, t2, t3, t4, t5, t6, t7, t8, t9;
 register int lbv, ubv;
/* Start of CLooG code */
if (_PB_N >= 1) {
  for (t2=0;t2<=floord(_PB_N-2,32);t2++) {
    for (t4=t2;t4<=floord(_PB_N-1,32);t4++) {
      for (t5=32*t2;t5<=min(min(_PB_N-2,32*t2+31),32*t4+30);t5++) {
        for (t7=max(32*t4,t5+1);t7<=min(_PB_N-1,32*t4+31);t7++) {
          R[t5][t7] = SCALAR_VAL(0.0);;
        }
      }
    }
  }
  for (t2=0;t2<=_PB_N-1;t2++) {
    nrm = SCALAR_VAL(0.0);;
    for (t4=0;t4<=_PB_M-1;t4++) {
      nrm += A[t4][t2] * A[t4][t2];;
    }
    R[t2][t2] = SQRT_FUN(nrm);;
    for (t4=0;t4<=floord(_PB_M-1,32);t4++) {
      for (t5=32*t4;t5<=min(_PB_M-1,32*t4+31);t5++) {
        Q[t5][t2] = A[t5][t2] / R[t2][t2];;
      }
    }
    if ((_PB_M >= 1) && (t2 <= _PB_N-2)) {
      for (t4=ceild(t2-30,32);t4<=floord(_PB_N-1,32);t4++) {
        for (t6=0;t6<=floord(_PB_M-1,32);t6++) {
          int __up1 = min(_PB_N-1,32*t4+31);
          for (t7=max(32*t4,t2+1);t7<=__up1-1;t7+=2) {
            DATA_TYPE __r0 = R[t2][t7];
            DATA_TYPE __r1 = R[t2][(t7+1)];
            for (t9=32*t6;t9<=min(_PB_M-1,32*t6+31)-1;t9+=2) {
              __r0 += Q[t9][t2] * A[t9][t7];;
              __r0 += Q[(t9+1)][t2] * A[(t9+1)][t7];;
              __r1 += Q[t9][t2] * A[t9][(t7+1)];;
              __r1 += Q[(t9+1)][t2] * A[(t9+1)][(t7+1)];;
            }
            R[t2][t7] = __r0;
            R[t2][(t7+1)] = __r1;
          }
          for (;t7<=__up1;t7++) {
            DATA_TYPE __r0 = R[t2][t7];
            for (t9=32*t6;t9<=min(_PB_M-1,32*t6+31)-1;t9+=2) {
              __r0 += Q[t9][t2] * A[t9][t7];;
              __r0 += Q[(t9+1)][t2] * A[(t9+1)][t7];;
            }
            R[t2][t7] = __r0;
          }
        }
        for (t6=0;t6<=floord(_PB_M-1,32);t6++) {
          int __up2 = min(_PB_N-1,32*t4+31);
          for (t7=max(32*t4,t2+1);t7<=__up2-1;t7+=2) {
            DATA_TYPE __r0 = R[t2][t7];
            DATA_TYPE __r1 = R[t2][(t7+1)];
            for (t9=32*t6;t9<=min(_PB_M-1,32*t6+31)-1;t9+=2) {
              A[t9][t7] = A[t9][t7] - Q[t9][t2] * __r0;;
              A[(t9+1)][t7] = A[(t9+1)][t7] - Q[(t9+1)][t2] * __r0;;
              A[t9][(t7+1)] = A[t9][(t7+1)] - Q[t9][t2] * __r1;;
              A[(t9+1)][(t7+1)] = A[(t9+1)][(t7+1)] - Q[(t9+1)][t2] * __r1;;
            }
          }
          for (;t7<=__up2;t7++) {
            DATA_TYPE __r0 = R[t2][t7];
            for (t9=32*t6;t9<=min(_PB_M-1,32*t6+31)-1;t9+=2) {
              A[t9][t7] = A[t9][t7] - Q[t9][t2] * __r0;;
              A[(t9+1)][t7] = A[(t9+1)][t7] - Q[(t9+1)][t2] * __r0;;
            }
          }
        }
      }
    }
  }
}
/* End of CLooG code */

}
