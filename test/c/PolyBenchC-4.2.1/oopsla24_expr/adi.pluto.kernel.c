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
/* adi.c: this file is part of PolyBench/C */

#include <stdio.h>
#include <unistd.h>
#include <string.h>
#include <math.h>

/* Include polybench common header. */
#include <polybench.h>

/* Include benchmark-specific header. */
#include "adi.h"


void kernel_adi(int tsteps, int n,
		DATA_TYPE POLYBENCH_2D(u,N,N,n,n),
		DATA_TYPE POLYBENCH_2D(v,N,N,n,n),
		DATA_TYPE POLYBENCH_2D(p,N,N,n,n),
		DATA_TYPE POLYBENCH_2D(q,N,N,n,n))
{
  int t, i, j;
  DATA_TYPE DX, DY, DT;
  DATA_TYPE B1, B2;
  DATA_TYPE mul1, mul2;
  DATA_TYPE a, b, c, d, e, f;
#define CAST_DTYPE(x) ((DATA_TYPE)x)

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
DX = SCALAR_VAL(1.0)/CAST_DTYPE(_PB_N);;
DY = SCALAR_VAL(1.0)/CAST_DTYPE(_PB_N);;
DT = SCALAR_VAL(1.0)/CAST_DTYPE(_PB_TSTEPS);;
B1 = SCALAR_VAL(2.0);;
B2 = SCALAR_VAL(1.0);;
mul1 = B1 * DT / (DX * DX);;
mul2 = B2 * DT / (DY * DY);;
a = -mul1 / SCALAR_VAL(2.0);;
b = SCALAR_VAL(1.0)+mul1;;
c = a;;
d = -mul2 / SCALAR_VAL(2.0);;
e = SCALAR_VAL(1.0)+mul2;;
f = d;;
if (_PB_TSTEPS >= 3) {
  for (t2=1;t2<=_PB_N;t2++) {
    for (t4=0;t4<=floord(_PB_TSTEPS-2,32);t4++) {
      for (t7=max(1,32*t4);t7<=min(_PB_TSTEPS-2,32*t4+31);t7++) {
        v[0][t7] = SCALAR_VAL(1.0);;
      }
      for (t7=max(1,32*t4);t7<=min(_PB_TSTEPS-2,32*t4+31);t7++) {
        p[t7][0] = SCALAR_VAL(0.0);;
      }
      for (t7=max(1,32*t4);t7<=min(_PB_TSTEPS-2,32*t4+31);t7++) {
        q[t7][0] = v[0][t7];;
      }
      for (t6=0;t6<=floord(_PB_TSTEPS-2,32);t6++) {
        for (t7=max(1,32*t4);t7<=min(_PB_TSTEPS-2,32*t4+31)-1;t7+=2) {
          for (t9=max(1,32*t6);t9<=min(_PB_TSTEPS-2,32*t6+31)-1;t9+=2) {
            p[t7][t9] = -c / (a*p[t7][t9-1]+b);;
            q[t7][t9] = (-d*u[t9][t7-1]+(SCALAR_VAL(1.0)+SCALAR_VAL(2.0)*d)*u[t9][t7] - f*u[t9][t7+1]-a*q[t7][t9-1])/(a*p[t7][t9-1]+b);;
            p[t7][(t9+1)] = -c / (a*p[t7][(t9+1)-1]+b);;
            q[t7][(t9+1)] = (-d*u[(t9+1)][t7-1]+(SCALAR_VAL(1.0)+SCALAR_VAL(2.0)*d)*u[(t9+1)][t7] - f*u[(t9+1)][t7+1]-a*q[t7][(t9+1)-1])/(a*p[t7][(t9+1)-1]+b);;
            p[(t7+1)][t9] = -c / (a*p[(t7+1)][t9-1]+b);;
            q[(t7+1)][t9] = (-d*u[t9][(t7+1)-1]+(SCALAR_VAL(1.0)+SCALAR_VAL(2.0)*d)*u[t9][(t7+1)] - f*u[t9][(t7+1)+1]-a*q[(t7+1)][t9-1])/(a*p[(t7+1)][t9-1]+b);;
            p[(t7+1)][(t9+1)] = -c / (a*p[(t7+1)][(t9+1)-1]+b);;
            q[(t7+1)][(t9+1)] = (-d*u[(t9+1)][(t7+1)-1]+(SCALAR_VAL(1.0)+SCALAR_VAL(2.0)*d)*u[(t9+1)][(t7+1)] - f*u[(t9+1)][(t7+1)+1]-a*q[(t7+1)][(t9+1)-1])/(a*p[(t7+1)][(t9+1)-1]+b);;
          }
          for (;t9<=min(_PB_TSTEPS-2,32*t6+31);t9++) {
            p[t7][t9] = -c / (a*p[t7][t9-1]+b);;
            q[t7][t9] = (-d*u[t9][t7-1]+(SCALAR_VAL(1.0)+SCALAR_VAL(2.0)*d)*u[t9][t7] - f*u[t9][t7+1]-a*q[t7][t9-1])/(a*p[t7][t9-1]+b);;
            p[(t7+1)][t9] = -c / (a*p[(t7+1)][t9-1]+b);;
            q[(t7+1)][t9] = (-d*u[t9][(t7+1)-1]+(SCALAR_VAL(1.0)+SCALAR_VAL(2.0)*d)*u[t9][(t7+1)] - f*u[t9][(t7+1)+1]-a*q[(t7+1)][t9-1])/(a*p[(t7+1)][t9-1]+b);;
          }
        }
        for (;t7<=min(_PB_TSTEPS-2,32*t4+31);t7++) {
          for (t9=max(1,32*t6);t9<=min(_PB_TSTEPS-2,32*t6+31);t9++) {
            p[t7][t9] = -c / (a*p[t7][t9-1]+b);;
            q[t7][t9] = (-d*u[t9][t7-1]+(SCALAR_VAL(1.0)+SCALAR_VAL(2.0)*d)*u[t9][t7] - f*u[t9][t7+1]-a*q[t7][t9-1])/(a*p[t7][t9-1]+b);;
          }
        }
      }
      for (t7=max(1,32*t4);t7<=min(_PB_TSTEPS-2,32*t4+31);t7++) {
        v[_PB_N-1][t7] = SCALAR_VAL(1.0);;
      }
      for (t6=ceild(-_PB_TSTEPS-29,32);t6<=-1;t6++) {
        for (t7=max(1,32*t4);t7<=min(_PB_TSTEPS-2,32*t4+31)-1;t7+=2) {
          for (t9=max(32*t6,-_PB_TSTEPS+2);t9<=32*t6+31-1;t9+=2) {
            v[-t9][t7] = p[t7][-t9] * v[-t9+1][t7] + q[t7][-t9];;
            v[-(t9+1)][t7] = p[t7][-(t9+1)] * v[-(t9+1)+1][t7] + q[t7][-(t9+1)];;
            v[-t9][(t7+1)] = p[(t7+1)][-t9] * v[-t9+1][(t7+1)] + q[(t7+1)][-t9];;
            v[-(t9+1)][(t7+1)] = p[(t7+1)][-(t9+1)] * v[-(t9+1)+1][(t7+1)] + q[(t7+1)][-(t9+1)];;
          }
        }
        for (;t7<=min(_PB_TSTEPS-2,32*t4+31);t7++) {
          for (t9=max(32*t6,-_PB_TSTEPS+2);t9<=32*t6+31;t9++) {
            v[-t9][t7] = p[t7][-t9] * v[-t9+1][t7] + q[t7][-t9];;
          }
        }
      }
    }
    for (t4=0;t4<=floord(_PB_TSTEPS-2,32);t4++) {
      for (t7=max(1,32*t4);t7<=min(_PB_TSTEPS-2,32*t4+31);t7++) {
        u[t7][0] = SCALAR_VAL(1.0);;
      }
      for (t7=max(1,32*t4);t7<=min(_PB_TSTEPS-2,32*t4+31);t7++) {
        p[t7][0] = SCALAR_VAL(0.0);;
      }
      for (t7=max(1,32*t4);t7<=min(_PB_TSTEPS-2,32*t4+31);t7++) {
        q[t7][0] = u[t7][0];;
      }
      for (t6=0;t6<=floord(_PB_TSTEPS-2,32);t6++) {
        for (t7=max(1,32*t4);t7<=min(_PB_TSTEPS-2,32*t4+31)-1;t7+=2) {
          for (t9=max(1,32*t6);t9<=min(_PB_TSTEPS-2,32*t6+31)-1;t9+=2) {
            p[t7][t9] = -f / (d*p[t7][t9-1]+e);;
            q[t7][t9] = (-a*v[t7-1][t9]+(SCALAR_VAL(1.0)+SCALAR_VAL(2.0)*a)*v[t7][t9] - c*v[t7+1][t9]-d*q[t7][t9-1])/(d*p[t7][t9-1]+e);;
            p[t7][(t9+1)] = -f / (d*p[t7][(t9+1)-1]+e);;
            q[t7][(t9+1)] = (-a*v[t7-1][(t9+1)]+(SCALAR_VAL(1.0)+SCALAR_VAL(2.0)*a)*v[t7][(t9+1)] - c*v[t7+1][(t9+1)]-d*q[t7][(t9+1)-1])/(d*p[t7][(t9+1)-1]+e);;
            p[(t7+1)][t9] = -f / (d*p[(t7+1)][t9-1]+e);;
            q[(t7+1)][t9] = (-a*v[(t7+1)-1][t9]+(SCALAR_VAL(1.0)+SCALAR_VAL(2.0)*a)*v[(t7+1)][t9] - c*v[(t7+1)+1][t9]-d*q[(t7+1)][t9-1])/(d*p[(t7+1)][t9-1]+e);;
            p[(t7+1)][(t9+1)] = -f / (d*p[(t7+1)][(t9+1)-1]+e);;
            q[(t7+1)][(t9+1)] = (-a*v[(t7+1)-1][(t9+1)]+(SCALAR_VAL(1.0)+SCALAR_VAL(2.0)*a)*v[(t7+1)][(t9+1)] - c*v[(t7+1)+1][(t9+1)]-d*q[(t7+1)][(t9+1)-1])/(d*p[(t7+1)][(t9+1)-1]+e);;
          }
          for (;t9<=min(_PB_TSTEPS-2,32*t6+31);t9++) {
            p[t7][t9] = -f / (d*p[t7][t9-1]+e);;
            q[t7][t9] = (-a*v[t7-1][t9]+(SCALAR_VAL(1.0)+SCALAR_VAL(2.0)*a)*v[t7][t9] - c*v[t7+1][t9]-d*q[t7][t9-1])/(d*p[t7][t9-1]+e);;
            p[(t7+1)][t9] = -f / (d*p[(t7+1)][t9-1]+e);;
            q[(t7+1)][t9] = (-a*v[(t7+1)-1][t9]+(SCALAR_VAL(1.0)+SCALAR_VAL(2.0)*a)*v[(t7+1)][t9] - c*v[(t7+1)+1][t9]-d*q[(t7+1)][t9-1])/(d*p[(t7+1)][t9-1]+e);;
          }
        }
        for (;t7<=min(_PB_TSTEPS-2,32*t4+31);t7++) {
          for (t9=max(1,32*t6);t9<=min(_PB_TSTEPS-2,32*t6+31);t9++) {
            p[t7][t9] = -f / (d*p[t7][t9-1]+e);;
            q[t7][t9] = (-a*v[t7-1][t9]+(SCALAR_VAL(1.0)+SCALAR_VAL(2.0)*a)*v[t7][t9] - c*v[t7+1][t9]-d*q[t7][t9-1])/(d*p[t7][t9-1]+e);;
          }
        }
      }
      for (t7=max(1,32*t4);t7<=min(_PB_TSTEPS-2,32*t4+31);t7++) {
        u[t7][_PB_N-1] = SCALAR_VAL(1.0);;
      }
      for (t6=ceild(-_PB_TSTEPS-29,32);t6<=-1;t6++) {
        for (t7=max(1,32*t4);t7<=min(_PB_TSTEPS-2,32*t4+31)-1;t7+=2) {
          for (t9=max(32*t6,-_PB_TSTEPS+2);t9<=32*t6+31-1;t9+=2) {
            u[t7][-t9] = p[t7][-t9] * u[t7][-t9+1] + q[t7][-t9];;
            u[t7][-(t9+1)] = p[t7][-(t9+1)] * u[t7][-(t9+1)+1] + q[t7][-(t9+1)];;
            u[(t7+1)][-t9] = p[(t7+1)][-t9] * u[(t7+1)][-t9+1] + q[(t7+1)][-t9];;
            u[(t7+1)][-(t9+1)] = p[(t7+1)][-(t9+1)] * u[(t7+1)][-(t9+1)+1] + q[(t7+1)][-(t9+1)];;
          }
        }
        for (;t7<=min(_PB_TSTEPS-2,32*t4+31);t7++) {
          for (t9=max(32*t6,-_PB_TSTEPS+2);t9<=32*t6+31;t9++) {
            u[t7][-t9] = p[t7][-t9] * u[t7][-t9+1] + q[t7][-t9];;
          }
        }
      }
    }
  }
}
/* End of CLooG code */
}
