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
/* covariance.c: this file is part of PolyBench/C */

#include <stdio.h>
#include <unistd.h>
#include <string.h>
#include <math.h>

/* Include polybench common header. */
#include <polybench.h>

/* Include benchmark-specific header. */
#include "covariance.h"


void kernel_covariance(int m, int n,
		       DATA_TYPE float_n,
		       DATA_TYPE POLYBENCH_2D(data,N,M,n,m),
		       DATA_TYPE POLYBENCH_2D(cov,M,M,m,m),
		       DATA_TYPE POLYBENCH_1D(mean,M,m))
{
  int i, j, k;

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
  int t1, t2, t3, t4, t5, t6, t7, t8;
 register int lbv, ubv;
/* Start of CLooG code */
if (_PB_M >= 1) {
  for (t2=0;t2<=floord(_PB_M-1,32);t2++) {
    for (t3=t2;t3<=floord(_PB_M-1,32);t3++) {
      for (t4=32*t2;t4<=min(_PB_M-1,32*t2+31);t4++) {
        for (t5=max(32*t3,t4);t5<=min(_PB_M-1,32*t3+31);t5++) {
          cov[t4][t5] = SCALAR_VAL(0.0);;
        }
      }
    }
  }
  for (t2=0;t2<=floord(_PB_M-1,32);t2++) {
    for (t3=32*t2;t3<=min(_PB_M-1,32*t2+31);t3++) {
      mean[t3] = SCALAR_VAL(0.0);;
    }
  }
  if (_PB_N >= 1) {
    for (t2=0;t2<=floord(_PB_M-1,32);t2++) {
      for (t3=0;t3<=floord(_PB_N-1,32);t3++) {
        for (t4=32*t2;t4<=min(_PB_M-1,32*t2+31);t4++) {
          for (t5=32*t3;t5<=min(_PB_N-1,32*t3+31);t5++) {
            mean[t4] += data[t5][t4];;
          }
        }
      }
    }
  }
  for (t2=0;t2<=floord(_PB_M-1,32);t2++) {
    for (t3=32*t2;t3<=min(_PB_M-1,32*t2+31);t3++) {
      mean[t3] /= float_n;;
    }
  }
  for (t2=0;t2<=floord(_PB_N-1,32);t2++) {
    for (t3=0;t3<=floord(_PB_M-1,32);t3++) {
      for (t4=32*t2;t4<=min(_PB_N-1,32*t2+31);t4++) {
        for (t5=32*t3;t5<=min(_PB_M-1,32*t3+31);t5++) {
          data[t4][t5] -= mean[t5];;
        }
      }
    }
  }
  if (_PB_N >= 1) {
    for (t2=0;t2<=floord(_PB_M-1,32);t2++) {
      for (t3=t2;t3<=floord(_PB_M-1,32);t3++) {
        for (t4=0;t4<=floord(_PB_N-1,32);t4++) {
          for (t5=32*t2;t5<=min(_PB_M-1,32*t2+31)-1;t5+=2) {
            if (t5>32*t3-1) {
              t6 = t5;
              for (t7=32*t4;t7<=min(_PB_N-1,32*t4+31);t7++) {
                cov[t5][t6] += data[t7][t5] * data[t7][t6];;
              }
            }
            int __up = min(_PB_M-1,32*t3+31);
            for (t6=max(32*t3,t5+1);t6<=__up-1;t6+=2) {
              DATA_TYPE __r0 = cov[t5][t6];
              DATA_TYPE __r1 = cov[t5][(t6+1)];
              DATA_TYPE __r2 = cov[(t5+1)][t6];
              DATA_TYPE __r3 = cov[(t5+1)][(t6+1)];
              for (t7=32*t4;t7<=min(_PB_N-1,32*t4+31);t7++) {
                __r0 += data[t7][t5] * data[t7][t6];;
                __r1 += data[t7][t5] * data[t7][(t6+1)];;
                __r2 += data[t7][(t5+1)] * data[t7][t6];;
                __r3 += data[t7][(t5+1)] * data[t7][(t6+1)];;
              }
              cov[t5][t6] = __r0;
              cov[t5][(t6+1)] = __r1;
              cov[(t5+1)][t6] = __r2;
              cov[(t5+1)][(t6+1)] = __r3;
            }
            for (;t6<=__up;t6++) {
              DATA_TYPE __r0 = cov[t5][t6];
              DATA_TYPE __r2 = cov[(t5+1)][t6];
              for (t7=32*t4;t7<=min(_PB_N-1,32*t4+31);t7++) {
                __r0 += data[t7][t5] * data[t7][t6];;
                __r2 += data[t7][(t5+1)] * data[t7][t6];;
              }
              cov[t5][t6] = __r0;
              cov[(t5+1)][t6] = __r2;
            }
          }
        }
      }
    }
  }
  for (t2=0;t2<=floord(_PB_M-1,32);t2++) {
    for (t3=t2;t3<=floord(_PB_M-1,32);t3++) {
      for (t4=32*t2;t4<=min(_PB_M-1,32*t2+31);t4++) {
        for (t5=max(32*t3,t4);t5<=min(_PB_M-1,32*t3+31);t5++) {
          cov[t4][t5] /= (float_n - SCALAR_VAL(1.0));;
          cov[t5][t4] = cov[t4][t5];;
        }
      }
    }
  }
}
/* End of CLooG code */

}