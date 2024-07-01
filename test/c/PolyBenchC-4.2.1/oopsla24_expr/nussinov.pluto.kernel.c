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
/* nussinov.c: this file is part of PolyBench/C */

#include <stdio.h>
#include <unistd.h>
#include <string.h>
#include <math.h>

/* Include polybench common header. */
#include <polybench.h>

/* Include benchmark-specific header. */
#include "nussinov.h"

/* RNA bases represented as chars, range is [0,3] */
typedef char base;

#define match(b1, b2) (((b1)+(b2)) == 3 ? 1 : 0)
#define max_score(s1, s2) ((s1 >= s2) ? s1 : s2)


void kernel_nussinov(int n, base POLYBENCH_1D(seq,N,n),
			   DATA_TYPE POLYBENCH_2D(table,N,N,n,n))
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
  int t1, t2, t3, t4, t5, t6, t7, t8, t9, t10;
 register int lbv, ubv;
/* Start of CLooG code */
if (_PB_N >= 2) {
  for (t2=ceild(-_PB_N-29,32);t2<=0;t2++) {
    for (t4=max(0,-t2-1);t4<=floord(_PB_N-1,32);t4++) {
      if ((t2 <= floord(-_PB_N+2,32)) && (t4 >= ceild(_PB_N-31,32))) {
        table[(_PB_N-2)][(_PB_N-1)] = max_score(table[(_PB_N-2)][(_PB_N-1)], table[(_PB_N-2)][(_PB_N-1)-1]);;
        table[(_PB_N-2)][(_PB_N-1)] = max_score(table[(_PB_N-2)][(_PB_N-1)], table[(_PB_N-2)+1][(_PB_N-1)]);;
        table[(_PB_N-2)][(_PB_N-1)] = max_score(table[(_PB_N-2)][(_PB_N-1)], table[(_PB_N-2)+1][(_PB_N-1)-1]);;
      }
      if ((t2 == -t4-1) && (t2 >= ceild(-_PB_N,32))) {
        table[(-32*t2-2)][(-32*t2-1)] = max_score(table[(-32*t2-2)][(-32*t2-1)], table[(-32*t2-2)][(-32*t2-1)-1]);;
        table[(-32*t2-2)][(-32*t2-1)] = max_score(table[(-32*t2-2)][(-32*t2-1)], table[(-32*t2-2)+1][(-32*t2-1)]);;
        table[(-32*t2-2)][(-32*t2-1)] = max_score(table[(-32*t2-2)][(-32*t2-1)], table[(-32*t2-2)+1][(-32*t2-1)-1]);;
      }
      for (t5=max(max(32*t2,-_PB_N+3),-32*t4-29);t5<=min(min(0,32*t2+31),-32*t4+1);t5++) {
        table[-t5][(-t5+1)] = max_score(table[-t5][(-t5+1)], table[-t5][(-t5+1)-1]);;
        table[-t5][(-t5+1)] = max_score(table[-t5][(-t5+1)], table[-t5+1][(-t5+1)]);;
        table[-t5][(-t5+1)] = max_score(table[-t5][(-t5+1)], table[-t5+1][(-t5+1)-1]);;
        for (t7=-t5+2;t7<=min(_PB_N-1,32*t4+31);t7++) {
          table[-t5][t7] = max_score(table[-t5][t7], table[-t5][t7-1]);;
          table[-t5][t7] = max_score(table[-t5][t7], table[-t5+1][t7]);;
          table[-t5][t7] = max_score(table[-t5][t7], table[-t5+1][t7-1]+match(seq[-t5], seq[t7]));;
          DATA_TYPE __r0 = table[-t5][t7];
          int __up1 = t7-1;
          for (t9=-t5+1;t9<=__up1-3;t9+=4) {
            __r0 = max_score(__r0, table[-t5][t9] + table[t9+1][t7]);;
            __r0 = max_score(__r0, table[-t5][(t9+1)] + table[(t9+1)+1][t7]);;
            __r0 = max_score(__r0, table[-t5][(t9+2)] + table[(t9+2)+1][t7]);;
            __r0 = max_score(__r0, table[-t5][(t9+3)] + table[(t9+3)+1][t7]);;
          }
          for (;t9<=__up1;t9++) {
            __r0 = max_score(__r0, table[-t5][t9] + table[t9+1][t7]);;
          }
          table[-t5][t7] = __r0;
        }
      }
      for (t5=max(32*t2,-32*t4+2);t5<=min(0,32*t2+31);t5++) {
        for (t7=32*t4;t7<=min(_PB_N-1,32*t4+31);t7++) {
          table[-t5][t7] = max_score(table[-t5][t7], table[-t5][t7-1]);;
          table[-t5][t7] = max_score(table[-t5][t7], table[-t5+1][t7]);;
          table[-t5][t7] = max_score(table[-t5][t7], table[-t5+1][t7-1]+match(seq[-t5], seq[t7]));;
          DATA_TYPE __r0 = table[-t5][t7];
          int __up2 = t7-1;
          for (t9=-t5+1;t9<=__up2-3;t9+=4) {
            __r0 = max_score(__r0, table[-t5][t9] + table[t9+1][t7]);;
            __r0 = max_score(__r0, table[-t5][(t9+1)] + table[(t9+1)+1][t7]);;
            __r0 = max_score(__r0, table[-t5][(t9+2)] + table[(t9+2)+1][t7]);;
            __r0 = max_score(__r0, table[-t5][(t9+3)] + table[(t9+3)+1][t7]);;
          }
          for (;t9<=__up2;t9++) {
            __r0 = max_score(__r0, table[-t5][t9] + table[t9+1][t7]);;
          }
          table[-t5][t7] = __r0;
        }
      }
    }
  }
}
/* End of CLooG code */

}
