[TOC]

# Overview

This is an instruction on how to evaluate the artifact of our project in our paper *Fully Verified Instruction Scheduling: a lightweight and flexible approach*.



# Environment Configuration

### System requirement

**Hosting OS**: only tested on Linux machine

**Dependencies for mechanized proof**

- **coq**, version 8.15.0 

- **menhir**, version 20220210, An LR(1) parser generator

**Dependencies for generating an executable files**

- **ocaml**, version 4.14.0, the OCaml compiler (virtual package)
- **ctypes**, version 0.20.1, combinators for binding to C libraries without writing any C
- **ctypes-foreign**, version 0.18.0, virtual package for enabling the ctypes.foreign subpackage
- **dune**, version 3.13.0, fast, portable, and opinionated build system

**Dependencies for experiments**:

- **Hardware:** an <u>in-order Risc-V</u> machine architecture (e.g. SiFive U74)
- **Software: **no additional software requirements to run the experiments



### Build the system

**Step 1: install dependencies**

1. Install [opam](https://opam.ocaml.org/) package manager on your machine

2. Install all the dependencies of mechanized proofs using opam

```shell
opam install coq=8.15.0 menhir=20220210 
```

​		Theses ensure that you can check our formal proofs 

3. Install all the dependencies of generating executable file of the compiler

```shell
opam install ocaml=4.14.0 ctypes=0.20.1 ctypes-foreign=0.18.0 dune=3.13.0
```

​		These ensures generating the final executable files successfully

4. Install all the dependences of running experiments: TODO

**Step 2: build both the proofs and executable files**

1. Clone [our project](https://github.com/Youngzt998/CompCertDev) file at your local machine, and switch to branch dune-ffi

   ```
   git clone git@github.com:Youngzt998/CompCertDev.git
   git checkout dune-ffi
   ```

2. At the root path,  run the configure script

   ```shell
   ./configure rv64-linux
   ```

   *Note 1: while this is the same configuration command as the original CompCert, other machine architecture is not supported in this artifact*

   *Note 2: you may run this configure on a different architecture like x86 and can still check the proof part and build an executable file, but the generated compiler cannot run as normal or be used for experiments*

3. Build the system by issuing the command

   ```shell
   make all
   ```

   or parallel build on an N-core machine it by

   ```
   make -j N all
   ```

   This takes almost the same building process as the original CompCert, i,e, it checks all the Coq proofs, then extracts OCaml code from the Coq specification and combines it with supporting hand-written Caml code to generate the executable for CompCert. The *.ml files will be linked successfully and generating the executable files.

   An expected error message could occur at the end of making, <u>if you are not building the system on Risc-V machine</u>:

   ```
   gcc: error: unrecognized argument in option ‘-mabi=lp64d’
   make[2]: *** [i64_stof.o] Error 2
   gcc: note: valid arguments to ‘-mabi=’ are: ms sysv
   ccomp: error: preprocessor command failed with exit code 1 (use -v to see invocation)
   
   1 error detected.
   Makefile:65: recipe for target 'i64_udivmod.o' failed
   make[2]: *** [i64_udivmod.o] Error 2
   make[2]: Leaving directory '/home/zyang638/coq-compcert-variants/test/CompCertDev/runtime'
   Makefile:226: recipe for target 'runtime' failed
   make[1]: *** [runtime] Error 2
   make[1]: Leaving directory '/home/zyang638/coq-compcert-variants/test/CompCertDev'
   Makefile:181: recipe for target 'all' failed
   make: *** [all] Error 2
   ```

   This means you have generated an executable compiler program targeting Risc-V, but it fails initial tests on a none-Risc-V machine. It will not influence the evaluation on mechanized proofs. However, the experiments part will not be able to run.

   

   If you ever run *make clean* after the first building, make sure to run the following command before re-building the projects to avoid a version issue.

   ```
   make -f Makefile.extr clean
   make
   ```

   

4. Check the generated compiler executable file ***ccomp*** at the root path of the project file. This is the compiler we used to run the performance evaluation.

**Step 4: Run our experiments**：in the final section



# Mechanized Proofs in the Paper

This section provides reference of all the algorithms, lemmas and theorems implemented in our paper.

### Project files

The whole project was developed based on CompCert-3.12. The following files belongs to this research paper

- **Mechanized proofs:** All the lemmas and theorems implemented in this paper was collected in a single file *<u>backend/Scheduling.v</u>*. To evaluate the result of our mechanized proof, open the project in some IDE (e.g. VSCode) after installing and building the proof through the makefile.

- **Scheduling heuristics:** 

  <u>*./my/Prioritizer.ml*</u>	is the heuristic function in OCaml, that used a C function to compute the priority of scheduling, and was used by instruction scheduling passes in Coq

  ./my/oracle_sched.c is the heuristic function in C to compute the priority of scheduling

​	    ./my/ORACLE_SCHED.md is the documentation on how scheduling heuristics work

### Proof structures

The mechanized proof in file *<u>backend/Scheduling.v</u>* consists of the following parts:

- **Line 46~765**, *Section TRY_SWAP, TOPO_REORDER, LIST_TOPO, SWAPPING_PROPERTY, TRY_SWAP_NUM*: 

  Properties on abstract topo-logical sort

- **Line 768~826**, *Section SIMULATION_SEQUENCE*: 

  Additional properties on general CompCert framework

- **Line 832~868**, *Section MACHINE_DEPENDENT_RISCV*:

  Machine dependent proofs (Risc-V)

- **Line 870~910**: *Section MACHINE_DEPENDENT_X86* (commented): 

  Machine dependent proofs (x86_64), 

- **Line 912~1523**:

  Lemmas about the intermediate language *Linear* that we used to do instruction scheduling

- **Line 1525~2221**, *Section SINGLE_SWAP_CORRECTNESS*: 

  Lemmas about semantics preservation after only swapping one pair of adjacent independent instructions inside only one function block

- **Line 2224~2282:** 

  Lemmas about composing a sequence of swapping operation

- **Line 2285~2455**, *Section ABSTRACT_SCHEDULER*: 

  Abstract definition of a valid scheduler (hypothesis on what relation should be satisfied between original and scheduled instructions), and proof of forward simulation under such hypothesis 

- **Line 2462~2623**, *Section ABSTRACT_LIST_SCHEDULER*: 

  Concrete definition of a list scheduler, while the scheduling heuristic is still abstracted as an parameter

- **Line 2627~3067**,  *Section ABSTRACT_LIST_SCHEDULER*: 

  Correctness proof of the list scheduler

- **Line 3074~3221**: 

  Instantiating the scheduling heuristic using outside heuristic (implemented in OCaml code)

- **Line 3225~3230**: 

  Semantics preservation of the actual scheduler we used to run experiments

*Note: the length of proof code is shorter than the proof length we claimed in paper due to some proof refinement after the submission*



### Axioms, assumptions, and unfinished parts of the proof

Our artifact contains 100% mechanized proof of all the theorems in our paper. There is no unfinished proofs. The proof is based on the original CompCert (version 3.12), and does not involves any new axioms/assumptions. It has exact the same trust base as the original CompCert's framework.

***Notes:** linking is not currently supported, which is also not in the result of our paper. The theorems we implemented only guarantee the whole compiler correctness.* 



### Instruction Scheduler Implemented

#### a. Scheduler codes in Coq

You may locate the functions corresponding ***Algorithm 2.*** in our paper at Section ABSTRACT_LIST_SCHEDULER by locating the following defininition:

```
Variable prioritizer: list instruction -> list positive.

Definition DPTree_t := PTree.t (instruction * PS.t).
...
Fixpoint dep_pset (i: instruction) (l_rev: numblock): PS.t := 
...
Fixpoint dep_tree (l_rev: numblock): DPTree_t :=
...
Definition dep_tree_gen (nl: list (positive * instruction)) :=
...
Definition indep_nodes (m : DPTree_t) :=
Definition schedule_1 ...
Fixpoint schedule_n ...
Definition schedule_numblock (nl: list (positive * instruction)) := ...
Definition list_schedule' := schedule_program schedule_numblock.
```

The scheduling heuristic (prioritizer) was abstracted away. At line 3081, it was instantiated as Coq's interface with OCaml function

```
Parameter prioritizer : list int -> int -> list (list int) -> int -> (list int).

Definition prioritizer' (l: list instruction): list positive :=
  let nodes := block2ids l in
  let edges := nblock2edges (numlistgen l) in
  let prior' :=
    prioritizer
      nodes (int_of_nat (length nodes))
      edges (int_of_nat (length edges)) in
   List.map pos_of_int prior'   .
```

And the final instruction scheduling pass was defined as

```
Definition transf_program := list_schedule' prioritizer'.
```



#### b. Scheduler codes in OCaml and C

The file <u>*./my/Prioritizer.ml*</u> contains the heuristic function in OCaml. It has exactly the same interface as the Coq parameter

```ocaml
let prioritizer nodes n edges m: int list = ...
```

This OCaml function further used a C function by using tools Ctypes

```ocaml
let result =
    C.Functions.prioritizer (CArray.start nodes_arr) n (CArray.start edges_arr) m
in
...
```

The C function is defined in the file *<u>./my/oracle_sched.c</u>*

```C
int *prioritizer(int *nodes, int n, int **edges, int m) {
	...
}
```



### Locate the final theorem

The final theorem of this paper was located at the end of the file *<u>./backend/Scheduling.v</u>*

```
Theorem list_schedule_forward_simulation:
forall prog tprog, transf_program prog = OK tprog -> 
  forward_simulation (Linear.semantics prog) (Linear.semantics tprog).
Proof.
  intros. eapply abstract_list_schedule_forward_simulation; eauto.
Qed.
```

You may run 

```
Print Assumptions list_schedule_forward_simulation.
```

at Coq to check that we did not introduced different assumptions than the original CompCert.



### Paper-to-artifact correspondence guide

You may follow this guide to locate all the definition, lemmas and theorems claimed mathematically in our paper in our mechanized proof. Note that all proofs is collected under file *<u>./backend/Scheduling.v</u>*

***Definition 9*** (Topo-sorted List): Under section TOPO_REORDER

```
Inductive topo_sorted: list A -> Prop := ...
```

***Definition 10*** (Generated Order by Position, GOP): 

```
Variable R: A -> A -> Prop.
Variable l: list A.
Inductive GenR' (i: positive) (na1 na2: positive * A): Prop :=
  GenR_intro: List.In na1 (numlistgen' l i) -> List.In na2 (numlistgen' l i) -> 
    fst na1 < fst na2 -> R (snd na1) (snd na2)  -> GenR' i na1 na2.
Definition GenR := GenR' 1.
```

*Note: the function numlistgen pairs elements in a list with its index at the list*

***Lemma 4.*** A list is topo-sorted by its own GOP, under section LIST_TOPO

```
Lemma tsorted_self: tsorted (numlistgen l).
```

***Definition 11*** (Swapping Attempt), under section TRY_SWAP

```
Fixpoint try_swap (n: nat) (l: list A): list A := ...
Fixpoint try_swap_seq (ln: list nat) (la: list A): list A := ...
```

***Definition 12*** (Topological reorder)

```
Inductive topo_reorder : list A -> list A -> Prop :=
| topo_reorder_nil: topo_reorder [] []
| topo_reorder_skip x l l' : ngt x l -> topo_reorder l l' -> topo_reorder (x::l) (x::l')
| topo_reorder_swap x y l : (~ R x y) -> (~ R y x) -> topo_reorder (y::x::l) (x::y::l)
| topo_reorder_trans l l' l'' :
  topo_reorder l l' -> topo_reorder l' l'' -> topo_reorder l l''.
```

*Note: as we mentioned in the paper, the mechanized proof used a different version of definition that already contains the concept of "swapping" for simpler proofs*

***Lemma 5.*** (Swapping Lemma)

The mechanized proof of the inductive proof in the paper consists of the following lemmas/theorems:

Firstly, prove two topo-sorted lists with same elements is a topo_reorder of each other by induction on the length of a list:

```
Lemma sorted_same_elements_topo_reorder_ind:
  forall n,
    (forall k l1 l2, k < n -> length l1 = k -> NoDupSame l1 l2 ->  
              topo_sorted l1 -> topo_sorted l2 -> topo_reorder l1 l2) ->
    (forall l1 l2, length l1 = n -> NoDupSame l1 l2 ->  
              topo_sorted l1 -> topo_sorted l2 -> topo_reorder l1 l2) .

Theorem sorted_same_elements_topo_reorder: 
    forall l1 l2,  NoDupSame l1 l2 -> 
      topo_sorted l1 -> topo_sorted l2 -> topo_reorder l1 l2.
```

Since the definition of topo-reorder already contains the concepts of swapping, the proof of the above lemmas exactly matches the proof of **Lemma 5** in the paper.

Then the following theorem matches the description of **Lemma 5** in the paper

```
Theorem swapping_property:
  forall l nl', (treorder R l) (numlistgen l) nl' -> 
    exists ln, nl' = try_swap_seq Rbnum ln (numlistgen l).
```



***Definition 14.*** (Dependence Relation)

```
Definition happens_before (i1 i2: instruction): bool := ...
```



***Definition 13.*** (Instruction Scheduler), ***Definition 15.*** (Valid Instruction Scheduler) 

Under section ABSTRACT_SCHEDULER, they were written as an abstract parameter of a section.

```
Variable schedule': list (positive * instruction) -> res (list (positive * instruction)).

Hypothesis schedule_valid:
  forall l nl', schedule' (numlistgen l) = OK nl' -> 
    treorder HBR l (numlistgen l) nl'.
```

 and ***Lemma 6.*** (decomposing lemma)

```
Lemma swapping_lemma_numblock:
  forall l nl', schedule' (numlistgen l) = OK nl' ->
      exists ln, nl' = try_swap_seq HBnum ln (numlistgen l).
```

***Definition 16.*** (Single Swapper) at line 1359 and 1378

```
Fixpoint try_swap_prog_def_in_one (pos: nat) (n: nat) (prog_defs: list (ident * globdef fundef unit)): list (ident * globdef fundef unit) := ...     
Definition transf_program_try_swap_in_one (pos: nat) (n: nat) (p: program): res program:= 
...
```

***Definition 17.*** (Composing Scheduler)  at line 1381

```
Fixpoint try_swap_prog_def_seq (seq: list (nat * nat)) (prog_defs: list (ident * globdef fundef unit)):= ...
```

***Lemma 7.*** (correctness of single swapper) at line 2227

```
Lemma transf_program_single_swap_forward_simulation:
  forall pos n prog tprog, 
    transf_program_try_swap_in_one pos n prog = OK tprog ->
    	forward_simulation (Linear.semantics prog) (Linear.semantics tprog).
```

***Lemma 8.*** (Any valid instruction scheduler preserved forward simulation relarion). at section ABSTRACT_SCHEDULER

```
Theorem schedule_program_forward_simulation:
 forall prog tprog: program, schedule_program prog = OK tprog ->
  forward_simulation (Linear.semantics prog) (Linear.semantics tprog).
```

***Lemma 9.*** Graph construction correctness

```
Lemma dep_tree_sound: ...
Lemma dep_tree_complete: ...
```

***Definition 18.*** (Scheduling invariant)

```
Inductive schedule_invariant (l: list instruction) (original: DPTree_t)
    (scheduled: list (positive * instruction)) (remain: DPTree_t) : Prop :=
...
```

***Lemma 10.*** (Invariant Preservation)

```
Lemma initial_invariant_preserve: ...
Lemma schedule_1_invariant_preserve: ...
Lemma schedule_n_invariant_preserve: ...
Lemma final_invariant_preserve: ...
```

***Lemma 12.*** (Our implementation is a valid scheduler)

```
Lemma schedule_numblock_correct:
  forall l nl', schedule_numblock (numlistgen l) = OK nl' ->
    treorder HBR l (numlistgen l) nl'.
```

***Theorem 1.*** Scheduler in Algorithm 2 preserved the forward simulation relation

```
Theorem abstract_list_schedule_forward_simulation:
  forall prog tprog, list_schedule' prog = OK tprog -> 
    forward_simulation (Linear.semantics prog) (Linear.semantics tprog).
Proof.
  intros. eapply schedule_program_forward_simulation; eauto.
  eapply schedule_numblock_correct.
Qed.
```



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
After the above step, there are two binaries generated for each input benchmark, e.g., `2mm.pluto.base` and `2mm.pluto.sche` for `2mm.pluto.kernel.c` benchmark, respectively corresponding to the baseline version CompCert 3.13.1 and our version with instruction scheduling for a RISC-V in-order processor.
```shell
   ./2mm.pluto.base >& 2mm_base_output.txt
   ./2mm.pluto.sche >& 2mm_sche_output.txt
```
The executed output shows the kernel execution time in seconds and computation results.

