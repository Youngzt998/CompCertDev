# Oracle scheduler

Given instruction-level data dependence graph, this module returns the
scheduling priority based on heuristic algorithms (Critical Path
method or Slack method).

* `oracle_sched.c`: Define all functions, enums, and cost table.
* `headers/oracle_sched.h`: Header for top-level function `prioritizer`.

## Interface

```
int *prioritizer(int *nodes, int n, int **edges, int m);
```

* Arguments
  * `nodes`: 1-D array with size of `n`
    * A node contains its instruction ID, e.g., ID = 1 for ADD
  * `edges`: 2-D array with size of `m` x 2
    * An edge is pair of {src_idx, dest_idx}
    * 1 <= src_idx, dest_idx <= `n`
      * Assuming Coq-based list indexing that starts from `1`
* Return
  * `priority`: 1-D array with size of `n`

### Example

Let's consider the following basic block with three instructions and
two dependence edges.

```
  t1 = 1.23 + 2.34;  // FADD.D (cost = 7)
  t2 = 4.56 / 3.21;  // FDIV.D (cost = 33)
  t3 = t1 - t2;      // FSUB.D (cost = 7)

//  (FADD.D)  (FDIV.D)
//         \  /
//          \/
//       (FSUB.D)
```

The corresponding `nodes` and `edges` are shown below.

Note that: The array indexing is to start from `1` (instead of `0` for C standard array) according to the indexing in the overall scheduler implementations in Coq.

```
  nodes[3] = {104 /* FADD.D */, 107 /* FDIV.D */, 105 /* FSUB.D */};
  edges[2] = {{1,3}, {2,3}};
```

And the return value `priority` is shown below (when CP method is used).

```
  priority == {14, 40, 7};
```

## Instruction IDs and costs

The instruction IDs for SiFive U74 RISC-V core are assigned as part of
the instruction cost table `cost_table_u74riscv`.

```
#define NUM_INSTS_U74RISCV 220
static int cost_table_u74riscv[NUM_INSTS_U74RISCV] = {
  1,  // id 0: default (wild card)

  // R-Type Integer Instructions (Table 36)
  1,  // id 1: ADD
  1,  // id 2: SUB
  ...

  // Double-Precision FP Computational Instructions (Table 63, latency from Table 178)
  7,  // id 104: FADD.D
  7,  // id 105: FSUB.D
  7,  // id 106: FMUL.D
  33, // id 107: FDIV.D  (9-58, average: 33.5)
  ...
```

Note that SiFive U74 RISC-V core is the only architecture whose cost
table is currently supported.

## Scheduling heuristics

Critical Path method and Slack method are currently implemented as the
heuristics to determine scheduling priority.

```
typedef enum _alg_type {
  ALG_UNDEF = -1,
  ALG_CP,
  ALG_SLACK,
} Alg_type;
...

int *prioritizer(int *nodes, int n, int **edges, int m) {
  int alg_type_id = 0;  // ALG_CP
  int arc_type_id = 0;  // ARC_U74RISCV
  ... 
```

To use Slack method, set `alg_type_id = 1;` above.
