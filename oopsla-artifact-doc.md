# Overview

This is an instruction on how to evaluate the result of our project in our paper *Fully Verified Instruction Scheduling: a lightweight and flexible approach*.



# Environment Configuration

### System requirement

**Dependencies for mechanized proof**

coq            8.15.0      version 8.15.0

menhir         20220210    An LR(1) parser generator

**Dependencies for generating an executable files **

ocaml  				4.14.0      The OCaml compiler (virtual package)
ctypes         		0.20.1      Combinators for binding to C libraries without writing any C
ctypes-foreign   0.18.0      Virtual package for enabling the ctypes.foreign subpackage
dune           		3.13.0      Fast, portable, and opinionated build system

**Dependencies for experiments** : TODO

- **Hardware:** Risc-V machine





### Build the system

**Step 1: install dependencies**

1. Install [opam](https://opam.ocaml.org/) package manager on your machine

2. Install all the dependencies of mechanized proofs using opam

```shell
opam install coq=8.15.0 menhir=20220210 
```

3. Install all the dependencies of generating executable file of the compiler

```shell
opam install ocaml=4.14.0 ctypes.0.20.1 ctypes-foreign.0.18.0 dune.3.13.0
```

4. Install all the dependences of running experiments: TODO



**Step 2: build both the proofs and executable files **

1. Clone our project file

2. At the root path,  run the configure script

   ```shell
   ./configure rv64-linux
   ```

   *Note: while this is the same configuration command as the original CompCert, other machine architecture is not supported in this artifact*

3. Build the system by issuing the command

   ```shell
   make all
   ```

   or parallel build it by

   ```
   make -j N all
   ```

   This takes almost the same building process as the original CompCert, i,e, it checks all the Coq proofs, then extracts Caml code from the Coq specification and combines it with supporting hand-written Caml code to generate the executable for CompCert.

4. Check the generated compiler executable file *ccomp* at the root path of the project file. This is the compiler we used to run the performance evaluation.

**Step 4: Run our experiments **

TODO.



# Functions and lemmas in the paper

This section provides reference of all the algorithms, lemmas and theorems implemented in our paper.

### Related files

- **Mechanized proof:** All the lemmas and theorems implemented in this paper was collected in a single file *<u>backend/Scheduling.v</u>*. To evaluate the result of our mechanized proof, open the project in some IDE (e.g. VSCode) after installing and building the proof through the makefile.

- **Scheduling heuristics:** 

  <u>*./my/Prioritizer.ml*</u> 		the heuristic function in OCaml, that used a C function to compute the priority of scheduling, and was used by instruction scheduling passes in Coq

  ./my/oracle_sched.c	the heuristic function in C to compute the priority of scheduling

​	    ./my/ORACLE_SCHED.md 		documentation on how scheduling heuristics work

### Proof structures

- line 46~765:  Properties on abstract topo-logical sort
- line 768~826: additional properties on general framework
- line 832~868: machine dependent proofs (Risv-V)
- line 870~910: machine dependent proofs (x86_64), commented
- line 912~1523: lemmas about the intermediate language Linear that we used to do instruction scheduling
- line 1525~2221: lemmas about semantics preservation after only swapping one pair of adjacent independent instructions inside only one function block
- line 2224~2282: lemmas about composing a sequence of swapping operation
- line 2285~2455 : abstract definition of a valid scheduler (hypothesis on what relation should be satisfied between original and scheduled instructions), and proof of forward simulation under such hypothesis 
- line 2462~2623: concrete definition of a list scheduler, while the scheduling heuristic is abstracted as an parameter
- line 2627~3067: semantics preservation of the list scheduler
- line 3074~3221: instantiating the scheduling heuristic using outside prioritizer (implemented in OCaml code)
- line 3225~3230: semantics preservation of the actual scheduler we used to run experiments



### Paper-to-artifact correspondence guide

TODO



### Axioms, assumptions, and unfinished parts of the proof

Our artifact should contains 100% mechanized proof of all the theorems in our paper. There is no unfinished proofs. The proof is based on the original CompCert (version 3.12), and does not involves any new axioms/assumptions. It has exact the same trust base as the original CompCert's framework.

***Notes:** linking is not currently supported, which is also not in the result of our paper. The theorems we implemented only guarantee the whole compiler correctness.* 









# Run our experiments

In the performance experiments in Section 8.2, we used two versions of the CompCert compiler.
* Baseline: Original CompCert version 3.13.1
  * https://github.com/AbsInt/CompCert/tree/3.13
* Our work: This repository

## Preparation
Set the following two environmental variables to specify the baseline and our repository. Assuming they are located in directory `$OOPSLA24_AE_HOME` and respectively named as `CompCert` and `CompCertDev`, we can set them as follows:
```shell
   export COMPCERT_HOME_BASE=$OOPSLA24_AE_HOME/CompCert
   export COMPCERT_HOME_SCHE=$OOPSLA24_AE_HOME/CompCertDev 
   ```

Move to the following directory under `$COMPCERT_HOME_SCHE` (i.e., this repository) which contains all benchmark codes and compilation script.
```shell
   cd $COMPCERT_HOME_SCHE/test/c/PolyBenchC-4.2.1/oopsla24_expr/
   ```
## Compilation
To compile the benchmark programs, use `compile.sh` shell script that generates two versions of binaries compiled by the baseline and our version of CompCert.
The following command compiles all the benchmarks and shows the compilation times in seconds.
```shell
   ./compile.sh *.c
   ```

An example output is shown below, where `2mm.pluto.kernel.c` benchmark is compiled.
```shell
   ./compile.sh 2mm.pluto.kernel.c 
   Kernel compilation time measurements: 2mm.pluto.kernel.c for base (repeat 3 times)
   0.88user 0.31system 0:01.48elapsed 80%CPU (0avgtext+0avgdata 20624maxresident)k
   16104inputs+32outputs (95major+5087minor)pagefaults 0swaps
   0.87user 0.12system 0:01.01elapsed 98%CPU (0avgtext+0avgdata 20620maxresident)k
   8inputs+32outputs (0major+5131minor)pagefaults 0swaps
   0.88user 0.11system 0:01.02elapsed 97%CPU (0avgtext+0avgdata 20648maxresident)k
   8inputs+32outputs (0major+5131minor)pagefaults 0swaps
   Binary gen: 2mm.pluto.kernel.c for base
   Kernel compilation time measurements: 2mm.pluto.kernel.c for sche (repeat 3 times)
   2.74user 0.45system 0:03.82elapsed 83%CPU (0avgtext+0avgdata 72040maxresident)k
   16992inputs+9248outputs (100major+17821minor)pagefaults 0swaps
   2.81user 0.25system 0:03.13elapsed 98%CPU (0avgtext+0avgdata 71908maxresident)k
   8inputs+9248outputs (0major+17870minor)pagefaults 0swaps
   2.96user 0.16system 0:03.19elapsed 98%CPU (0avgtext+0avgdata 72040maxresident)k
   8inputs+9248outputs (0major+17865minor)pagefaults 0swaps
   Binary gen: 2mm.pluto.kernel.c for sche
   ```

## Run
After the above step, there are two binaries generated for each input benchmark, e.g., `2mm.pluto.base` and `2mm.pluto.sche`, respectively corresponding to the baseline version CompCert 3.13.1 and our version with instruction scheduling for a RISC-V in-order processor.
```shell
   ./2mm.pluto.base >& 2mm_base_output.txt
   ./2mm.pluto.sche >& 2mm_sche_output.txt
   ```
The executed output shows the kernel execution time in seconds and computation results.
