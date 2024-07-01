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
/* symm.c: this file is part of PolyBench/C */

#include <stdio.h>
#include <unistd.h>
#include <string.h>
#include <math.h>

/* Include polybench common header. */
#include <polybench.h>

/* Include benchmark-specific header. */
#include "symm.h"


void kernel_symm(int m, int n,
		 DATA_TYPE alpha,
		 DATA_TYPE beta,
		 DATA_TYPE POLYBENCH_2D(C,M,N,m,n),
		 DATA_TYPE POLYBENCH_2D(A,M,M,m,m),
		 DATA_TYPE POLYBENCH_2D(B,M,N,m,n))
{
  int i, j, k;
  DATA_TYPE POLYBENCH_2D(temp2,M,N,m,n);

//BLAS PARAMS
//SIDE = 'L'
//UPLO = 'L'
// =>  Form  C := alpha*A*B + beta*C
// A is MxM
// B is MxN
// C is MxN
//note that due to Fortran array layout, the code below more closely resembles upper triangular case in BLAS
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
  for (t2=0;t2<=floord(_PB_M-1,32);t2++) {
    for (t3=0;t3<=floord(_PB_N-1,32);t3++) {
      for (t4=32*t2;t4<=min(_PB_M-1,32*t2+31);t4++) {
        for (t5=32*t3;t5<=min(_PB_N-1,32*t3+31);t5++) {
          temp2[t4][t5] = 0;;
        }
      }
    }
  }
  if (_PB_M >= 2) {
    for (t2=0;t2<=floord(_PB_M-1,32);t2++) {
      for (t3=0;t3<=floord(_PB_N-1,32);t3++) {
        for (t4=0;t4<=min(floord(_PB_M-2,32),t2);t4++) {
          int __up1 = min(_PB_M-1,32*t2+31);
          for (t5=max(32*t2,32*t4+1);t5<=__up1-1;t5+=2) {
            for (t6=32*t3;t6<=min(_PB_N-1,32*t3+31)-1;t6+=2) {
              DATA_TYPE __r0 = temp2[t5][t6];
              DATA_TYPE __r1 = temp2[t5][(t6+1)];
              DATA_TYPE __r2 = temp2[(t5+1)][t6];
              DATA_TYPE __r3 = temp2[(t5+1)][(t6+1)];
              for (t7=32*t4;t7<=min(32*t4+31,t5-1);t7++) {
                __r0 += B[t7][t6] * A[t5][t7];;
                __r1 += B[t7][(t6+1)] * A[t5][t7];;
                __r2 += B[t7][t6] * A[(t5+1)][t7];;
                __r3 += B[t7][(t6+1)] * A[(t5+1)][t7];;
              }
              for (;t7<=min(32*t4+31,t5);t7++) {
                __r2 += B[t7][t6] * A[(t5+1)][t7];;
                __r3 += B[t7][(t6+1)] * A[(t5+1)][t7];;
              }
              temp2[t5][t6] = __r0;
              temp2[t5][(t6+1)] = __r1;
              temp2[(t5+1)][t6] = __r2;
              temp2[(t5+1)][(t6+1)] = __r3;
            }
          }
          for (;t5<=__up1;t5++) {
            for (t6=32*t3;t6<=min(_PB_N-1,32*t3+31)-1;t6+=2) {
              DATA_TYPE __r0 = temp2[t5][t6];
              DATA_TYPE __r1 = temp2[t5][(t6+1)];
              for (t7=32*t4;t7<=min(32*t4+31,t5-1);t7++) {
                __r0 += B[t7][t6] * A[t5][t7];;
                __r1 += B[t7][(t6+1)] * A[t5][t7];;
              }
              temp2[t5][t6] = __r0;
              temp2[t5][(t6+1)] = __r1;
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
          C[t4][t5] = beta * C[t4][t5] + alpha*B[t4][t5] * A[t4][t4] + alpha * temp2[t4][t5];;
        }
      }
    }
  }
  if (_PB_M >= 2) {
    for (t2=0;t2<=floord(_PB_N-1,32);t2++) {
      for (t3=0;t3<=floord(_PB_M-2,32);t3++) {
        for (t4=t3;t4<=floord(_PB_M-1,32);t4++) {
          for (t5=32*t2;t5<=min(_PB_N-1,32*t2+31)-1;t5+=2) {
            int __up2 = min(min(_PB_M-2,32*t3+31),32*t4+30);
            for (t6=32*t3;t6<=__up2-1;t6+=2) {
              DATA_TYPE __r0 = C[t6][t5];
              DATA_TYPE __r1 = C[(t6+1)][t5];
              DATA_TYPE __r2 = C[t6][(t5+1)];
              DATA_TYPE __r3 = C[(t6+1)][(t5+1)];
              if (t6+1>=32*t4) {
                t7=t6+1;
                __r0 += alpha*B[t7][t5] * A[t7][t6];;
                __r2 += alpha*B[t7][(t5+1)] * A[t7][t6];;
              }
              for (t7=max(32*t4,t6+2);t7<=min(_PB_M-1,32*t4+31);t7++) {
                __r0 += alpha*B[t7][t5] * A[t7][t6];;
                __r1 += alpha*B[t7][t5] * A[t7][(t6+1)];;
                __r2 += alpha*B[t7][(t5+1)] * A[t7][t6];;
                __r3 += alpha*B[t7][(t5+1)] * A[t7][(t6+1)];;
              }
              C[t6][t5] = __r0;
              C[(t6+1)][t5] = __r1;
              C[t6][(t5+1)] = __r2;
              C[(t6+1)][(t5+1)] = __r3;
            }
            for (;t6<=__up2;t6++) {
              DATA_TYPE __r0 = C[t6][t5];
              DATA_TYPE __r2 = C[t6][(t5+1)];
              for (t7=max(32*t4,t6+1);t7<=min(_PB_M-1,32*t4+31);t7++) {
                __r0 += alpha*B[t7][t5] * A[t7][t6];;
                __r2 += alpha*B[t7][(t5+1)] * A[t7][t6];;
              }
              C[t6][t5] = __r0;
              C[t6][(t5+1)] = __r2;
            }
          }
        }
      }
    }
  }
}
/* End of CLooG code */

}
