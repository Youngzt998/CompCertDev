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
/* doitgen.c: this file is part of PolyBench/C */

#include <stdio.h>
#include <unistd.h>
#include <string.h>
#include <math.h>

/* Include polybench common header. */
#include <polybench.h>

/* Include benchmark-specific header. */
#include "doitgen.h"


void kernel_doitgen(int nr, int nq, int np,
		    DATA_TYPE POLYBENCH_3D(A,NR,NQ,NP,nr,nq,np),
		    DATA_TYPE POLYBENCH_2D(C4,NP,NP,np,np),
		    DATA_TYPE POLYBENCH_1D(sum,NP,np))
{
  int r, q, p, s;
  DATA_TYPE POLYBENCH_3D(sum2,NR,NQ,NP,nr,nq,np);

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
if ((_PB_NP >= 1) && (_PB_NQ >= 1) && (_PB_NR >= 1)) {
  for (t2=0;t2<=floord(_PB_NR-1,32);t2++) {
    for (t3=0;t3<=floord(_PB_NQ-1,32);t3++) {
      for (t4=0;t4<=floord(_PB_NP-1,32);t4++) {
        for (t5=32*t2;t5<=min(_PB_NR-1,32*t2+31);t5++) {
          for (t6=32*t3;t6<=min(_PB_NQ-1,32*t3+31);t6++) {
            for (t7=32*t4;t7<=min(_PB_NP-1,32*t4+31);t7++) {
              sum2[t5][t6][t7] = SCALAR_VAL(0.0);;
            }
          }
        }
      }
    }
  }
  for (t2=0;t2<=floord(_PB_NR-1,32);t2++) {
    for (t3=0;t3<=floord(_PB_NQ-1,32);t3++) {
      for (t4=0;t4<=floord(_PB_NP-1,32);t4++) {
        for (t5=0;t5<=floord(_PB_NP-1,32);t5++) {
          for (t6=32*t2;t6<=min(_PB_NR-1,32*t2+31)-1;t6+=2) {
            for (t7=32*t3;t7<=min(_PB_NQ-1,32*t3+31)-1;t7+=2) {
              for (t8=32*t4;t8<=min(_PB_NP-1,32*t4+31)-1;t8+=2) {
                DATA_TYPE __r0 = sum2[t6][t7][t8];
                DATA_TYPE __r1 = sum2[t6][t7][(t8+1)];
                DATA_TYPE __r2 = sum2[t6][(t7+1)][t8];
                DATA_TYPE __r3 = sum2[t6][(t7+1)][(t8+1)];
                DATA_TYPE __r4 = sum2[(t6+1)][t7][t8];
                DATA_TYPE __r5 = sum2[(t6+1)][t7][(t8+1)];
                DATA_TYPE __r6 = sum2[(t6+1)][(t7+1)][t8];
                DATA_TYPE __r7 = sum2[(t6+1)][(t7+1)][(t8+1)];
                for (t9=32*t5;t9<=min(_PB_NP-1,32*t5+31);t9++) {
                  __r0 += A[t6][t7][t9] * C4[t9][t8];;
                  __r1 += A[t6][t7][t9] * C4[t9][(t8+1)];;
                  __r2 += A[t6][(t7+1)][t9] * C4[t9][t8];;
                  __r3 += A[t6][(t7+1)][t9] * C4[t9][(t8+1)];;
                  __r4 += A[(t6+1)][t7][t9] * C4[t9][t8];;
                  __r5 += A[(t6+1)][t7][t9] * C4[t9][(t8+1)];;
                  __r6 += A[(t6+1)][(t7+1)][t9] * C4[t9][t8];;
                  __r7 += A[(t6+1)][(t7+1)][t9] * C4[t9][(t8+1)];;
                }
                sum2[t6][t7][t8] = __r0;
                sum2[t6][t7][(t8+1)] = __r1;
                sum2[t6][(t7+1)][t8] = __r2;
                sum2[t6][(t7+1)][(t8+1)] = __r3;
                sum2[(t6+1)][t7][t8] = __r4;
                sum2[(t6+1)][t7][(t8+1)] = __r5;
                sum2[(t6+1)][(t7+1)][t8] = __r6;
                sum2[(t6+1)][(t7+1)][(t8+1)] = __r7;
              }
            }
          }
        }
      }
    }
  }
  for (t2=0;t2<=floord(_PB_NR-1,32);t2++) {
    for (t3=0;t3<=floord(_PB_NQ-1,32);t3++) {
      for (t4=0;t4<=floord(_PB_NP-1,32);t4++) {
        for (t5=32*t2;t5<=min(_PB_NR-1,32*t2+31);t5++) {
          for (t6=32*t3;t6<=min(_PB_NQ-1,32*t3+31);t6++) {
            for (t7=32*t4;t7<=min(_PB_NP-1,32*t4+31);t7++) {
              A[t5][t6][t7] = sum2[t5][t6][t7];;
            }
          }
        }
      }
    }
  }
}
/* End of CLooG code */

}
