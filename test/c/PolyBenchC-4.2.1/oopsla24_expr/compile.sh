#!/bin/sh 

# Set COMPCERT_HOME var 
# COMPCERT_HOME_BASE=$HOME/CompCert-3.13.1 
# COMPCERT_HOME_SCHE=/nethome/zyang638/CompCertDev 

# How many times to repeat for kernel compilation time measurements 
repeat=3

# Needed for some large benchmarks
ulimit -s unlimited

for src in $*
do
    for ver in 'base' 'sche'
    do
	echo "Kernel compilation time measurements: $src for $ver (repeat $repeat times)"
        i=1
        while [ $i -le $repeat ]; do
            if [ $ver = 'base' ]; then
                /usr/bin/time $COMPCERT_HOME_BASE/ccomp -L$COMPCERT_HOME_BASE/runtime -I ../utilities $src -S > .dummy_file.txt
            else
                /usr/bin/time $COMPCERT_HOME_SCHE/ccomp -L$COMPCERT_HOME_SCHE/runtime -I ../utilities $src -S > .dummy_file.txt
            fi
            i=`expr $i + 1`
        done
        knl=`echo $src | sed -e 's/\.c//g'`
	asm1=$knl.s
        asm2=$knl.$ver.s
        mv $asm1 $asm2

        echo "Binary gen: $src for $ver"
        app=`echo $src | sed -e 's/\.kernel\.c//g'`
        main=mains/$app.main.c
        bin=$app.$ver
        $COMPCERT_HOME_BASE/ccomp -L$COMPCERT_HOME_BASE/runtime -O3 -I ../utilities -I ./ ../utilities/polybench.c -DPOLYBENCH_TIME -DPOLYBENCH_DUMP_ARRAYS $asm2 $main -o $bin -lm 2> .dummy_file.txt
    done
done
rm .dummy_file.txt
