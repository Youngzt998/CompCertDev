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
/* jacobi-1d.c: this file is part of PolyBench/C */

#include <stdio.h>
#include <unistd.h>
#include <string.h>
#include <math.h>

/* Include polybench common header. */
#include <polybench.h>

/* Include benchmark-specific header. */
#include "jacobi-1d.h"


void kernel_jacobi_1d(int tsteps,
			    int n,
			    DATA_TYPE POLYBENCH_1D(A,N,n),
			    DATA_TYPE POLYBENCH_1D(B,N,n))
{
  int t, i;

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
if ((_PB_N >= 3) && (_PB_TSTEPS >= 1)) {
  for (t1=0;t1<=floord(_PB_TSTEPS-1,32);t1++) {
    for (t2=2*t1;t2<=min(floord(2*_PB_TSTEPS+_PB_N-3,32),floord(64*t1+_PB_N+61,32));t2++) {
      if (t1 <= floord(32*t2-_PB_N+1,64)) {
        if ((_PB_N+1)%2 == 0) {
          A[(_PB_N-2)] = 0.33333 * (B[(_PB_N-2)-1] + B[(_PB_N-2)] + B[(_PB_N-2) + 1]);;
        }
      }
      for (t3=max(ceild(32*t2-_PB_N+2,2),32*t1);t3<=min(min(_PB_TSTEPS-1,32*t1+31),16*t2+14);t3++) {
        if (t2 <= floord(t3,16)) {
          B[1] = 0.33333 * (A[1 -1] + A[1] + A[1 + 1]);;
        }
        int __up = min(32*t2+31,2*t3+_PB_N-2);
        for (t4=max(32*t2,2*t3+2);t4<=__up-3;t4+=4) {
          B[(-2*t3+t4)] = 0.33333 * (A[(-2*t3+t4)-1] + A[(-2*t3+t4)] + A[(-2*t3+t4) + 1]);;
          A[(-2*t3+t4-1)] = 0.33333 * (B[(-2*t3+t4-1)-1] + B[(-2*t3+t4-1)] + B[(-2*t3+t4-1) + 1]);;
          B[(-2*t3+(t4+1))] = 0.33333 * (A[(-2*t3+(t4+1))-1] + A[(-2*t3+(t4+1))] + A[(-2*t3+(t4+1)) + 1]);;
          A[(-2*t3+(t4+1)-1)] = 0.33333 * (B[(-2*t3+(t4+1)-1)-1] + B[(-2*t3+(t4+1)-1)] + B[(-2*t3+(t4+1)-1) + 1]);;
          B[(-2*t3+(t4+2))] = 0.33333 * (A[(-2*t3+(t4+2))-1] + A[(-2*t3+(t4+2))] + A[(-2*t3+(t4+2)) + 1]);;
          A[(-2*t3+(t4+2)-1)] = 0.33333 * (B[(-2*t3+(t4+2)-1)-1] + B[(-2*t3+(t4+2)-1)] + B[(-2*t3+(t4+2)-1) + 1]);;
          B[(-2*t3+(t4+3))] = 0.33333 * (A[(-2*t3+(t4+3))-1] + A[(-2*t3+(t4+3))] + A[(-2*t3+(t4+3)) + 1]);;
          A[(-2*t3+(t4+3)-1)] = 0.33333 * (B[(-2*t3+(t4+3)-1)-1] + B[(-2*t3+(t4+3)-1)] + B[(-2*t3+(t4+3)-1) + 1]);;
        }
        for (;t4<=__up;t4++) {
          B[(-2*t3+t4)] = 0.33333 * (A[(-2*t3+t4)-1] + A[(-2*t3+t4)] + A[(-2*t3+t4) + 1]);;
          A[(-2*t3+t4-1)] = 0.33333 * (B[(-2*t3+t4-1)-1] + B[(-2*t3+t4-1)] + B[(-2*t3+t4-1) + 1]);;
        }
        if (t2 >= ceild(2*t3+_PB_N-32,32)) {
          A[(_PB_N-2)] = 0.33333 * (B[(_PB_N-2)-1] + B[(_PB_N-2)] + B[(_PB_N-2) + 1]);;
        }
      }
      if ((t1 >= ceild(t2-1,2)) && (t2 <= floord(_PB_TSTEPS-16,16))) {
        B[1] = 0.33333 * (A[1 -1] + A[1] + A[1 + 1]);;
      }
    }
  }
}
/* End of CLooG code */

}
