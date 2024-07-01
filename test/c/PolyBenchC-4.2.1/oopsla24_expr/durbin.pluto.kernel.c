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
/* durbin.c: this file is part of PolyBench/C */

#include <stdio.h>
#include <unistd.h>
#include <string.h>
#include <math.h>

/* Include polybench common header. */
#include <polybench.h>

/* Include benchmark-specific header. */
#include "durbin.h"


void kernel_durbin(int n,
		   DATA_TYPE POLYBENCH_1D(r,N,n),
		   DATA_TYPE POLYBENCH_1D(y,N,n))
{
 DATA_TYPE z[N];
 DATA_TYPE alpha;
 DATA_TYPE beta;
 DATA_TYPE sum;

 int i,k;

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
  int t1, t2, t3, t4;
 register int lbv, ubv;
/* Start of CLooG code */
alpha = -r[0];;
beta = SCALAR_VAL(1.0);;
y[0] = -r[0];;
for (t2=1;t2<=_PB_N-1;t2++) {
  sum = SCALAR_VAL(0.0);;
  sum += r[t2-0 -1]*y[0];;
  beta = (1-alpha*alpha)*beta;;
  int __up1 = t2-1;
  for (t3=1;t3<=__up1-3;t3+=4) {
    sum += r[t2-t3-1]*y[t3];;
    sum += r[t2-(t3+1)-1]*y[(t3+1)];;
    sum += r[t2-(t3+2)-1]*y[(t3+2)];;
    sum += r[t2-(t3+3)-1]*y[(t3+3)];;
  }
  for (;t3<=__up1;t3++) {
    sum += r[t2-t3-1]*y[t3];;
  }
  alpha = - (r[t2] + sum)/beta;;
  y[t2] = alpha;;
  int __up2 = 2*t2-1;
  for (t3=t2;t3<=__up2-3;t3+=4) {
    z[(-t2+t3)] = y[(-t2+t3)] + alpha*y[t2-(-t2+t3)-1];;
    z[(-t2+(t3+1))] = y[(-t2+(t3+1))] + alpha*y[t2-(-t2+(t3+1))-1];;
    z[(-t2+(t3+2))] = y[(-t2+(t3+2))] + alpha*y[t2-(-t2+(t3+2))-1];;
    z[(-t2+(t3+3))] = y[(-t2+(t3+3))] + alpha*y[t2-(-t2+(t3+3))-1];;
  }
  for (;t3<=__up2;t3++) {
    z[(-t2+t3)] = y[(-t2+t3)] + alpha*y[t2-(-t2+t3)-1];;
  }
  int __up3 = 3*t2-1;
  for (t3=2*t2;t3<=__up3-3;t3+=4) {
    y[(-2*t2+t3)] = z[(-2*t2+t3)];;
    y[(-2*t2+(t3+1))] = z[(-2*t2+(t3+1))];;
    y[(-2*t2+(t3+2))] = z[(-2*t2+(t3+2))];;
    y[(-2*t2+(t3+3))] = z[(-2*t2+(t3+3))];;
  }
  for (;t3<=__up3;t3++) {
    y[(-2*t2+t3)] = z[(-2*t2+t3)];;
  }
}
/* End of CLooG code */

}
