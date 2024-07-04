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



