#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

// #define DEBUG_ORACLE_SCHED
// #define INST_ID_AS_COST

/* ------------------------------------------------------------------------------------------ */
/*
   Instruction IDs and their cost table.
   Note: Currently support only SiFive U74 RISC-V core.
 */

typedef enum _arc_type {
  ARC_UNDEF = -1,
  ARC_U74RISCV,
} Arc_type;

/*
  Reference: SiFive U74-MC Core Complex Manual 21G1.01.00
   - https://starfivetech.com/uploads/u74mc_core_complex_manual_21G1.pdf
   - Chapter 6: Programmer’s Model
    -- Source of instruction list
   - Chapter 4: U7 RISC-V Core
    -- 4.3 Execution Pipeline
     --- The pipeline has a peak execution rate of two instructions per clock cycle,
         and is fully bypassed so that most instructions have a one-cycle result latency
          => One-cycle latency for default cost
    -- Table 18: U7 Instruction Latency
     --- Three-cycle latency for LOAD/MUL => used as load/multiply cost
     --- Six-cycle to 68-cycle latency for DIV/REM => used as division operation cost
   - Appendix C: Floating-Point Unit Instruction Timing
    -- Table 177: U7 Single-Precision FPU Instruction Latency and Repeat Rates
    -- Table 178: U7 Double-Precision FPU Instruction Latency and Repeat Rates

  Instruction-to-ID assignments:
   - The array indices in the following cost table are used as instruction IDs.
   - The ordering is based on the instruction description tables starting Table 36 in Chapter 6.
 */
#define NUM_INSTS_U74RISCV 220
static int cost_table_u74riscv[NUM_INSTS_U74RISCV] = {
  1,  // id 0: default (wild card)

  // R-Type Integer Instructions (Table 36)
  1,  // id 1: ADD
  1,  // id 2: SUB
  1,  // id 3: SLL
  1,  // id 4: SLT
  1,  // id 5: SLTU
  1,  // id 6: SRL
  1,  // id 7: SRA
  1,  // id 8: OR
  1,  // id 9: AND
  1,  // id 10: XOR

  // I-Type Integer Instructions (Table 38)
  1,  // id 11: ADDI
  1,  // id 12: SLTI
  1,  // id 13: SLTIU
  1,  // id 14: XORI
  1,  // id 15: ORI
  1,  // id 16: ANDI
  1,  // id 17: SLLI
  1,  // id 18: SRLI
  1,  // id 19: SRAI

  // I-Type Load Instructions (Table 40, latency from Table 18)
  3,  // id 20: LB
  3,  // id 21: LH
  3,  // id 22: LW
  3,  // id 23: LBU
  3,  // id 24: LHU

  // S-Type Store Instructions (Table 42)
  1,  // id 25: SB
  1,  // id 26: SH
  1,  // id 27: SW

  // J-Type Instructions (Table 43)
  1,  // id 28: JAL
  1,  // id 29: JALR

  // B-Type Instructions (Table 45)
  1,  // id 30: BEQ
  1,  // id 31: BNE
  1,  // id 32: BLT
  1,  // id 33: BGE
  1,  // id 34: BLTU
  1,  // id 35: BGEU

  // Multiplication Operations (Table 47, latency from Table 18)
  3,  // id 36: MUL
  3,  // id 37: MULH
  3,  // id 38: MULHU
  3,  // id 39: MULHSU
  3,  // id 40: MULW

  // Division Operations (Table 48, latency from Table 18)
  37, // id 41: DIV (6-68, average: 37, same for below)
  37, // id 42: DIVU
  37, // id 43: REM
  37, // id 44: REMU
  37, // id 45: DIVW
  37, // id 46: DIVUW
  37, // id 47: REMW
  37, // id 48: REMUW
  37, // id 49: MULDIV

  // Atomic Load-Reserve and Store-Conditional Instructions (Table 49)
  1,  // id 50: LR.W
  1,  // id 51: SC.W
  1,  // id 52: LR.D
  1,  // id 53: SC.D

  // Atomic Memory Operations (Table 50)
  1,  // id 54: AMOSWAP.W
  1,  // id 55: AMOADD.W
  1,  // id 56: AMOAND.W
  1,  // id 57: AMOOR.W
  1,  // id 58: AMOXOR.W
  1,  // id 59: AMOMIN.W
  1,  // id 60: AMOMINU.W
  1,  // id 61: AMOMAX.W
  1,  // id 62: AMOMAXU.W
  1,  // id 63: AMOSWAP.D
  1,  // id 64: AMOADD.D
  1,  // id 65: AMOAND.D
  1,  // id 66: AMOOR.D
  1,  // id 67: AMOXOR.D
  1,  // id 68: AMOMIN.D
  1,  // id 69: AMOMINU.D
  1,  // id 70: AMOMAX.D
  1,  // id 71: AMOMAXU.D

  // Single-Precision FP Load and Store Instructions (Table 53, latency from Table 177)
  2,  // id 72: FLW
  4,  // id 73: FSW

  // Single-Precision FP Computational Instructions (Table 54, latency from Table 177)
  5,  // id 74: FADD.S
  5,  // id 75: FSUB.S
  5,  // id 76: FMUL.S
  22, // id 77: FDIV.S (9-36, average: 22.5)
  18, // id 78: FSQRT.S (9-28, average: 18.5)
  2,  // id 79: FMIN.S
  2,  // id 80: FMAX.S
  5,  // id 81: FMADD.S
  5,  // id 82: FMSUB.S
  5,  // id 83: FNMADD.S
  5,  // id 84: FNMSUB.S

  // Single-Precision FP Conversion Instructions (Table 55, latency from Table 177)
  4,  // id 85: FCVT.W.S
  2,  // id 86: FCVT.S.W
  4,  // id 87: FCVT.WU.S
  2,  // id 88: FCVT.S.WU
  4,  // id 89: FCVT.L.S
  4,  // id 90: FCVT.S.L
  4,  // id 91: FCVT.LU.S
  4,  // id 92: FCVT.S.LU

  // Single-Precision FP to FP Sign-Injection Instructions (Table 56, latency from Table 177)
  2,  // id 93: FSGNJ.S
  2,  // id 94: FSGNJN.S
  2,  // id 95: FSGNJX.S

  // Single-Precision FP Move Instructions (Table 58, latency from Table 177)
  1,  // id 96: FMV.X.W
  2,  // id 97: FMV.W.X

  // Single-Precision FP Compare Instructions (Table 59, latency from Table 177)
  4,  // id 98:  FEQ.S
  4,  // id 99: FLT.S
  4,  // id 100: FLE.S

  // Single-Precision FP Classify Instructions (Table 60, latency from Table 177)
  4,  // id 101: FCLASS.S

  // Double-Precision FP Load and Store Instructions (Table 62, latency from Table 178)
  2,  // id 102: FLD
  4,  // id 103: FSD

  // Double-Precision FP Computational Instructions (Table 63, latency from Table 178)
  7,  // id 104: FADD.D
  7,  // id 105: FSUB.D
  7,  // id 106: FMUL.D
  33, // id 107: FDIV.D  (9-58, average: 33.5)
  33, // id 108: FSQRT.D (9-57, average: 33)
  2,  // id 109: FMIN.D
  2,  // id 110: FMAX.D
  7,  // id 111: FMADD.D
  7,  // id 112: FMSUB.D
  7,  // id 113: FNMADD.D
  7,  // id 114: FNMSUB.D

  // Double-Precision FP Conversion Instructions (Table 64, latency from Table 178)
  4,  // id 115: FCVT.W.D
  2,  // id 116: FCVT.D.W
  4,  // id 117: FCVT.WU.D
  2,  // id 118: FCVT.D.WU
  4,  // id 119: FCVT.L.D
  6,  // id 120: FCVT.D.L
  4,  // id 121: FCVT.LU.D
  6,  // id 122: FCVT.D.LU
  2,  // id 123: FCVT.S.D
  2,  // id 124: FCVT.D.S

  // Double-Precision FP to FP Sign-Injection Instructions (Table 65, latency from Table 178)
  2,  // id 125: FSGNJ.D
  2,  // id 126: FSGNJN.D
  2,  // id 127: FSGNJX.D

  // Double-Precision FP Move Instructions (Table 67, latency from Table 178)
  1,  // id 128: FMV.X.D
  6,  // id 129: FMV.D.X

  // Double-Precision FP Compare Instructions (Table 68, latency from Table 178)
  4,  // id 130: FEQ.D
  4,  // id 131: FLT.D
  4,  // id 132: FLE.D

  // Double-Precision FP Classify Instructions (Table 69, latency from Table 178)
  4,  // id 133: FCLASS.D

  // Stack-Pointed-Based Load Instructions (Table 70, latency from Table 18)
  3,  // id 134: C.LWSP
  3,  // id 135: C.LDSP
  3,  // id 136: C.LQSP
  3,  // id 137: C.FLWSP
  3,  // id 138: C.FLDSP

  // Stack-Pointed-Based Store Instructions (Table 71)
  1,  // id 139: C.LWSP
  1,  // id 140: C.SWSP
  1,  // id 141: C.SDSP
  1,  // id 142: C.SQSP
  1,  // id 143: C.FSWSP
  1,  // id 144: C.FSDSP

  // Register-Based Load Instructions (Table 72, latency from Table 18)
  3,  // id 145: C.LW
  3,  // id 146: C.LD
  3,  // id 147: C.LQ
  3,  // id 148: C.FLW
  3,  // id 149: C.FLD

  // Register-Based Store Instructions (Table 73)
  1,  // id 150: C.SW
  1,  // id 151: C.SD
  1,  // id 152: C.SQ
  1,  // id 153: C.FSW
  1,  // id 154: C.FSD

  // Unconditional Jump Instructions (Table 74)
  1,  // id 155: C.J
  1,  // id 156: C.JAL

  // Unconditional Control Transfer Instructions (Table 75)
  1,  // id 157: C.JR
  1,  // id 158: C.JALR

  // Conditional Control Transfer Instructions (Table 76)
  1,  // id 159: C.BEQZ
  1,  // id 160: C.BNEZ

  // Integer Constant-Generation Instructions (Table 77)
  1,  // id 161: C.LI
  1,  // id 162: C.LUI

  // Integer Register-Immediate Operations (Table 78-82)
  1,  // id 163: C.ADDI
  1,  // id 164: C.ADDIW
  1,  // id 165: C.ADDI16SP
  1,  // id 166: C.ADDI4SPN
  1,  // id 167: C.SLLI
  1,  // id 168: C.SRLI
  1,  // id 169: C.SRAI
  1,  // id 170: C.ANDI

  // Integer Register-Register Operations (Table 83)
  1,  // id 171: C.MV
  1,  // id 172: C.ADD

  // Integer Register-Register Operations (Table 84)
  1,  // id 173: C.AND
  1,  // id 174: C.OR
  1,  // id 175: C.XOR
  1,  // id 176: C.SUB
  1,  // id 177: C.ADDW
  1,  // id 178: C.SUBW

  // Count Leading/Trailing Zeroes Instructions (Table 85)
  1,  // id 179: CLZ
  1,  // id 180: CTZ
  1,  // id 181: CLZW
  1,  // id 182: CTZW

  // Count Bits Set Instructions (Table 86)
  1,  // id 183: CPOP
  1,  // id 184: CPOPW

  // Logic-With-Negate Instructions (Table 87)
  1,  // id 185: ANDN
  1,  // id 186: ORN
  1,  // id 187: XNOR

  // Comparison Instructions (Table 88)
  1,  // id 188: MIN
  1,  // id 189: MINU
  1,  // id 190: MAX
  1,  // id 191: MAXU

  // Sign-Extend Instructions (Table 89)
  1,  // id 192: SEXT.B
  1,  // id 193: SEXT.H

  // Bit Permutation Instructions (Table 90)
  1,  // id 194: ROR
  1,  // id 195: ROL
  1,  // id 196: RORI
  1,  // id 197: RORW
  1,  // id 198: ROLW
  1,  // id 199: RORIW

  // Address Calculation Instructions (Table 91)
  1,  // id 200: SH1ADD
  1,  // id 201: SH2ADD
  1,  // id 202: SH3ADD
  1,  // id 203: SH1ADD.UW
  1,  // id 204: SH2ADD.UW
  1,  // id 205: SH3ADD.UW

  // Add/Shift with Prefix Zero-Extend Instructions (Table 92)
  1,  // id 206: ADD.UW
  1,  // id 207: SLLI.UW

  // Bit Manipulation Pseudo-instructions (Table 93)
  1,  // id 208: ZEXT.H
  1,  // id 209: REV8
  1,  // id 210: ORC.B

  // Control and Status Register Instructions (Table 94)
  1,  // id 211: CSRRW
  1,  // id 212: CSRRS
  1,  // id 213: CSRRC
  1,  // id 214: CSRRWI
  1,  // id 215: CSRRSI
  1,  // id 216: CSRRCI

  // Timer and Counter Pseudo-instructions (Table 102)
  1,  // id 217: RDCYCLE
  1,  // id 218: RDTIME
  1,  // id 219: RDINSTRET
};

int get_inst_cost(int inst_id, Arc_type arc) {
  assert(0 <= inst_id);

  int cost = 0;
  switch (arc) {
  case ARC_U74RISCV:
    assert(inst_id < NUM_INSTS_U74RISCV);
    cost = cost_table_u74riscv[inst_id];
    break;
  default:
    assert(0);
  }

  return cost;
}

/* ------------------------------------------------------------------------------------------ */
typedef enum _alg_type {
  ALG_UNDEF = -1,
  ALG_CP,
  ALG_SLACK,
} Alg_type;

Alg_type get_alg_type(int type_id) {
  switch(type_id) {
  case 0:
    return ALG_CP;
    break;
  case 1:
    return ALG_SLACK;
    break;
  default:
    return ALG_UNDEF;
  }
}

Arc_type arc_type = ARC_UNDEF;
void set_arc_type(int type_id) {
  switch(type_id) {
  case 0:
    arc_type = ARC_U74RISCV;
    break;
  default:
    arc_type = ARC_UNDEF;
  }
}

int get_node_cost(int inst_id) {
#ifdef INST_ID_AS_COST
  // Debug/test mode to assume that inst_id represents instruction cost.
  int cost = inst_id;
#else
  int cost = get_inst_cost(inst_id, arc_type);
#endif  

#ifdef DEBUG_ORACLE_SCHED
  printf(" DEBUG: inst-%d cost: %d\n", inst_id, cost);
#endif
  return cost;
}

void warn_and_continue(const char *warning) {
  printf("Warning from oracle_sched.c: %s\n", warning);
}

int *calloc_and_init(int n, int val) {
  int *ret = (int *) calloc(n, sizeof(int));
  for (int i = 0; i < n; i++)
    ret[i] = val;
  return ret;
}

int verify_edges(int **edges, int m, int n) {
  for (int i = 0; i < m; i++) {
    for (int j = 0; j < 2; j++) {
      int id = edges[i][j];
      if (id < 0 || id >= n)
	return 0;
    }
  }
  return 1;
}

/*
  Dummy entry and exit:
   - Given graph with n nodes, add dummy entry (id = n) and exit (id = n+1) nodes.
   - Therefore, the total size of following arrays is n+2 (n regular nodes + 2 dummy nodes).
    -- 1-D array with size n+2
     --- path: Path length
     --- est: Earliest Start Time
     --- lst: Latest Start Time
    -- 2-D array with size of (n+2) x n
     --- pred: Predecessor ids
     --- succ: Successor ids

  2-D array pred and succ:
   - The predecessors/successors of node i (0 <= i <= n+1) are stored in pred[i]/succ[i].
    -- pred[i] and succ[i] are n-size array initialized by -1.
     --- Assuming n >= 1, any node has at most n predecessors/successors.
    -- predecessors/successors are left-aligned.
     --- E.g., node 3 has successors of 4, 5, 7, then: pred[3] = [4, 5, 7, -1, -1, ..., -1]
 */

/*
  Calculate pred or succ.
 */
int **calc_cessor(int **edges, int m, int n, int is_pred) {
  int **cessor = (int **) calloc(n+2, sizeof(int *));
  for (int i = 0; i < n+2; i++)
    cessor[i] = calloc_and_init(n, -1);

  for (int k = 0; k < m; k++) {
    int idx = is_pred ? edges[k][1] : edges[k][0];
    int val = is_pred ? edges[k][0] : edges[k][1];
    if (idx == val)
      continue;
    int j = 0;
    for (; j < n; j++) {
      if (cessor[idx][j] == -1 || cessor[idx][j] == val)
	break;
    }
    assert(j < n);
    if (cessor[idx][j] == -1)
      cessor[idx][j] = val;
  }
  return cessor;
}

/*
  node n: dummy entry node
  node n+1: dummy exit node
 */
void set_dummy_entry_and_exit(int **pred, int **succ, int n) {
  int j = 0;
  for (int i = 0; i < n; i++) {
    if (pred[i][0] == -1) {
      pred[i][0] = n;
      assert(j < n);
      succ[n][j] = i;
      j++;
    }
  }

  j = 0;
  for (int i = 0; i < n; i++) {
    if (succ[i][0] == -1) {
      succ[i][0] = n+1;
      assert(j < n);
      pred[n+1][j] = i;
      j++;
    }
  }

#ifdef DEBUG_ORACLE_SCHED
  for (int i = 0; i < n+2; i++) {
    for (int j = 0; j < n; j++) {
      if (pred[i][j] == -1)
	break;
      printf(" DEBUG: pred[%d][%d] = %d\n", i, j, pred[i][j]);
    }
  }
  for (int i = 0; i < n+2; i++) {
    for (int j = 0; j < n; j++) {
      if (succ[i][j] == -1)
	break;
      printf(" DEBUG: succ[%d][%d] = %d\n", i, j, succ[i][j]);
    }
  }
#endif
}

void traverse_and_set_time(int *nodes, int **children, int **parents, int *time, int curr, int n, int type) {
  for (int i = 0; i < n; i++) {
    int c = children[curr][i];
    if (c == -1)
      break;
    int cost_c = (c < n) ? get_node_cost(nodes[c]) : 0;
    int val = -1;
    int j = 0;
    for (; j < n; j++) {
      int p = parents[c][j];
      if (p == -1 || time[p] == -1)
	break;
      int cost_p = (p < n) ? get_node_cost(nodes[p]) : 0;
      switch (type) {
	int v;
      case 0:  // Path length: max_p(time[p] + cost_c)
	v = time[p] + cost_c;
	if (val == -1 || v > val)
	  val = v;
	break;
      case 1:  // EST: max_p(time[p] + cost_p)
	v = time[p] + cost_p;
	if (val == -1 || v > val)
	  val = v;
	break;
      case 2:  // LST: min_p(time[p] - cost_c)
	v = time[p] - cost_c;
	if (val == -1 || v < val)
	  val = v;
	break;
      default:
	assert(0);
      }
    }
    if (parents[c][j] == -1 || j == n) {
      assert(val >= 0);
      time[c] = val;
      traverse_and_set_time(nodes, children, parents, time, c, n, type);
    }
  }
}

int *calc_critical_path_length(int *nodes, int **pred, int **succ, int n) {
  int *path = calloc_and_init(n+2, -1);

  path[n+1] = 0;  // Path length for dummy exit node
  traverse_and_set_time(nodes, pred, succ, path, n+1, n, 0);
#ifdef DEBUG_ORACLE_SCHED
  for (int i = 0; i < n; i++)
    printf("DEBUG: path[%d] = %d\n", i, path[i]);
#endif

  return path;
}

int *calc_earliest_start_time(int *nodes, int **pred, int **succ, int n) {
  int *est = calloc_and_init(n+2, -1);

  est[n] = 0;  // EST for dummy entry node
  traverse_and_set_time(nodes, succ, pred, est, n, n, 1);
#ifdef DEBUG_ORACLE_SCHED
  for (int i = 0; i < n; i++)
    printf("DEBUG: est[%d] = %d\n", i, est[i]);
#endif

  return est;
}

int *calc_latest_start_time(int *nodes, int **pred, int **succ, int *est, int n) {
  int *lst = calloc_and_init(n+2, -1);

  lst[n+1] = est[n+1];  // LST for dummy exit node
  traverse_and_set_time(nodes, pred, succ, lst, n+1, n, 2);
#ifdef DEBUG_ORACLE_SCHED
  for (int i = 0; i < n; i++)
    printf("DEBUG: lst[%d] = %d\n", i, lst[i]);
#endif

  return lst;
}

void set_priority_cp(int *priority, int *nodes, int n, int **edges, int m) {
#ifdef DEBUG_ORACLE_SCHED
  printf("DEBUG: calling set_priority_cp\n");
#endif
  int **pred = calc_cessor(edges, m, n, 1);
  int **succ = calc_cessor(edges, m, n, 0);
  set_dummy_entry_and_exit(pred, succ, n);

  int *path = calc_critical_path_length(nodes, pred, succ, n);

  for (int i = 0; i < n; i++) {
    priority[i] = path[i];
  }

  for (int i = 0; i < n; i++) {
    free(pred[i]);
    free(succ[i]);
  }
  free(pred);
  free(succ);
  free(path);
}

void set_priority_slack(int *priority, int *nodes, int n, int **edges, int m) {
#ifdef DEBUG_ORACLE_SCHED
  printf("DEBUG: calling set_priority_slack\n");
#endif
  int **pred = calc_cessor(edges, m, n, 1);
  int **succ = calc_cessor(edges, m, n, 0);
  set_dummy_entry_and_exit(pred, succ, n);

  int *est = calc_earliest_start_time(nodes, pred, succ, n);
  int *lst = calc_latest_start_time(nodes, pred, succ, est, n);

  int max_slack = 0;
  int *slack = (int *) calloc(n, sizeof(int));
  for (int i = 0; i < n; i++) {
    slack[i] = lst[i] - est[i];
#ifdef DEBUG_ORACLE_SCHED
    printf("DEBUG: slack[%d] = %d\n", i, slack[i]);
#endif
    assert(slack[i] >= 0);
    if (slack[i] > max_slack)
      max_slack = slack[i];
  }
#ifdef DEBUG_ORACLE_SCHED
  printf("DEBUG: max_slack = %d\n", max_slack);
#endif
  for (int i = 0; i < n; i++) {
    priority[i] = max_slack - slack[i];
  }

  for (int i = 0; i < n; i++) {
    free(pred[i]);
    free(succ[i]);
  }
  free(pred);
  free(succ);
  free(est);
  free(lst);
  free(slack);
}

/*
  Arguments
   - nodes: 1-D array with size of n
    -- A node contains its instruction id, e.g., id = 1 for add
   - edges: 2-D array with size of m x 2
    -- An edge is pair of {src_idx, dest_idx}
    -- 0 <= src_idx, dest_idx < n
  Return
   - priority: 1-D array with size of n
*/
int *prioritizer_impl(int *nodes, int n, int **edges, int m, int alg_type_id, int arc_type_id) {
  char *warning = 0;
  int *priority = (int *) calloc(n, sizeof(int));

  set_arc_type(arc_type_id);
  if (arc_type == ARC_UNDEF)
    warning = "Unsupported architecture";

  if (!verify_edges(edges, m, n))
    warning = "Invalid edges";

  if (!warning) {
    /* Update priority array */
    switch (get_alg_type(alg_type_id)) {
    case ALG_CP:
      set_priority_cp(priority, nodes, n, edges, m);
      break;
    case ALG_SLACK:
      set_priority_slack(priority, nodes, n, edges, m);
      break;
    default:
      warn_and_continue("Unsupported heuristic algorithm");
    }
  } else {
    warn_and_continue(warning);
  }

  return priority;
}

int *prioritizer(int *nodes, int n, int **edges, int m) {
  int alg_type_id = 0;  // ALG_CP
  int arc_type_id = 0;  // ARC_U74RISCV
  int *priority = prioritizer_impl(nodes, n, edges, m, alg_type_id, arc_type_id);
  return priority;
}
