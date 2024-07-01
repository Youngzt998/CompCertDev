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
/* trisolv.c: this file is part of PolyBench/C */

#include <stdio.h>
#include <unistd.h>
#include <string.h>
#include <math.h>

/* Include polybench common header. */
#include <polybench.h>

/* Include benchmark-specific header. */
#include "trisolv.h"


void kernel_trisolv(int n,
		    DATA_TYPE POLYBENCH_2D(L,N,N,n,n),
		    DATA_TYPE POLYBENCH_1D(x,N,n),
		    DATA_TYPE POLYBENCH_1D(b,N,n))
{
  int i, j;

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
  int t1, t2, t3, t4, t5;
 register int lbv, ubv;
/* Start of CLooG code */
if (_PB_N >= 1) {
  for (t2=0;t2<=floord(_PB_N-1,32);t2++) {
    for (t3=32*t2;t3<=min(_PB_N-1,32*t2+31);t3++) {
      x[t3] = b[t3];;
    }
  }
  for (t2=0;t2<=floord(_PB_N-1,32);t2++) {
    for (t3=t2;t3<=floord(_PB_N-1,32);t3++) {
      if (t2 == t3) {
        for (t4=32*t2;t4<=min(_PB_N-2,32*t2+30);t4++) {
          x[t4] = x[t4] / L[t4][t4];;
          for (t5=t4+1;t5<=min(_PB_N-1,32*t2+31);t5++) {
            x[t5] -= L[t5][t4] * x[t4];;
          }
        }
      }
      if (t2 <= t3-1) {
        for (t4=32*t2;t4<=32*t2+31-1;t4+=2) {
          DATA_TYPE __r0 = x[t4];
          DATA_TYPE __r1 = x[(t4+1)];
          for (t5=32*t3;t5<=min(_PB_N-1,32*t3+31)-1;t5+=2) {
            x[t5] -= L[t5][t4] * __r0;;
            x[(t5+1)] -= L[(t5+1)][t4] * __r0;;
            x[t5] -= L[t5][(t4+1)] * __r1;;
            x[(t5+1)] -= L[(t5+1)][(t4+1)] * __r1;;
          }
        }
      }
      if ((t2 == t3) && (t2 >= ceild(_PB_N-31,32))) {
        x[(_PB_N-1)] = x[(_PB_N-1)] / L[(_PB_N-1)][(_PB_N-1)];;
      }
      if ((t2 == t3) && (t2 <= floord(_PB_N-32,32))) {
        x[(32*t2+31)] = x[(32*t2+31)] / L[(32*t2+31)][(32*t2+31)];;
      }
    }
  }
}
/* End of CLooG code */

}
