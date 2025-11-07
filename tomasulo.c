
#include <assert.h>
#include <limits.h>
#include <math.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>

#include "decode.def"
#include "dlite.h"
#include "host.h"
#include "instr.h"
#include "loader.h"
#include "machine.h"
#include "memory.h"
#include "misc.h"
#include "options.h"
#include "regs.h"
#include "sim.h"
#include "stats.h"
#include "syscall.h"

/* PARAMETERS OF THE TOMASULO'S ALGORITHM */

#define INSTR_QUEUE_SIZE 16

#define RESERV_INT_SIZE 5
#define RESERV_FP_SIZE 3
#define FU_INT_SIZE 3
#define FU_FP_SIZE 1

#define FU_INT_LATENCY 5
#define FU_FP_LATENCY 7

/* IDENTIFYING INSTRUCTIONS */

// unconditional branch, jump or call
#define IS_UNCOND_CTRL(op) \
  (MD_OP_FLAGS(op) & F_CALL || MD_OP_FLAGS(op) & F_UNCOND)

// conditional branch instruction
#define IS_COND_CTRL(op) (MD_OP_FLAGS(op) & F_COND)

// floating-point computation
#define IS_FCOMP(op) (MD_OP_FLAGS(op) & F_FCOMP)

// integer computation
#define IS_ICOMP(op) (MD_OP_FLAGS(op) & F_ICOMP)

// load instruction
#define IS_LOAD(op) (MD_OP_FLAGS(op) & F_LOAD)

// store instruction
#define IS_STORE(op) (MD_OP_FLAGS(op) & F_STORE)

// trap instruction
#define IS_TRAP(op) (MD_OP_FLAGS(op) & F_TRAP)

#define USES_INT_FU(op) (IS_ICOMP(op) || IS_LOAD(op) || IS_STORE(op))
#define USES_FP_FU(op) (IS_FCOMP(op))

#define WRITES_CDB(op) (IS_ICOMP(op) || IS_LOAD(op) || IS_FCOMP(op))

/* FOR DEBUGGING */

// prints info about an instruction
#define PRINT_INST(out, instr, str, cycle)    \
  myfprintf(out, "%d: %s", cycle, str);       \
  md_print_insn(instr->inst, instr->pc, out); \
  myfprintf(stdout, "(%d)\n", instr->index);

#define PRINT_REG(out, reg, str, instr)       \
  myfprintf(out, "reg#%d %s ", reg, str);     \
  md_print_insn(instr->inst, instr->pc, out); \
  myfprintf(stdout, "(%d)\n", instr->index);

/* VARIABLES */

// instruction queue for tomasulo
static instruction_t* instr_queue[INSTR_QUEUE_SIZE];
// number of instructions in the instruction queue
static int instr_queue_size = 0;

/* ECE552 Assignment 3 - BEGIN  CODE */

/* head and tail trackers for the instruction queue*/
static int instr_queue_head = 0;
static int instr_queue_tail = 0;

/* ECE552 Assignment 3 - END  CODE */

// reservation stations (each reservation station entry contains a pointer to an
// instruction)
static instruction_t* reservINT[RESERV_INT_SIZE];
static instruction_t* reservFP[RESERV_FP_SIZE];

// functional units
static instruction_t* fuINT[FU_INT_SIZE];
static instruction_t* fuFP[FU_FP_SIZE];

// common data bus
static instruction_t* commonDataBus = NULL;

// The map table keeps track of which instruction produces the value for each
// register
static instruction_t* map_table[MD_TOTAL_REGS];

// the index of the last instruction fetched
// Skip the first *0* invalid instruction 
static int fetch_index = 1;

// static instruction_t inst_debug;
// static instruction_t* inst_debug_ptr = &inst_debug;

/* FUNCTIONAL UNITS */

/* RESERVATION STATIONS */

/*
 * Description:
 * 	Checks if simulation is done by finishing the very last instruction
 *      Remember that simulation is done only if the entire pipeline is empty
 * Inputs:
 * 	sim_insn: the total number of instructions simulated
 * Returns:
 * 	True: if simulation is finished
 */
static bool is_simulation_done(counter_t sim_insn) {
  /* ECE552 Assignment 3 - BEGIN  CODE */
  /* the simulation is done if
   * (1) all instructions have been fetched i.e. fetch index >= sim_insn
   * (2) and no more instructions are in the pipeline */
  if (fetch_index > sim_insn) {
    /* checks IFQ */
    if (instr_queue_size != 0) {
      return 0;
    }

    /* check the pipeline */
    for (int i = 0; i < FU_FP_SIZE; i++) {
      if (fuFP[i] != NULL) {
        return 0;
      }
    }
    for (int i = 0; i < FU_INT_SIZE; i++) {
      if (fuINT[i] != NULL) {
        return 0;
      }
    }
    for (int i = 0; i < RESERV_FP_SIZE; i++) {
      if (reservFP[i] != NULL) {
        return 0;
      }
    }
    for (int i = 0; i < RESERV_INT_SIZE; i++) {
      if (reservINT[i] != NULL) {
        return 0;
      }
    }
    return 1;
  }
  return 0;
  /* ECE552 Assignment 3 - END  CODE */
}

/*
 * Description:
 * 	Retires the instruction from writing to the Common Data Bus
 * Inputs:
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void CDB_To_retire(int current_cycle) {
  /* ECE552 Assignment 3 - BEGIN  CODE */
  /* checks all RS and and map table and clears any entry that corresponds to be
   * current cdb*/
  /* bypass if commonDataBus is null */
  if (commonDataBus == NULL) {
    return;
  }
  /* checks map table clears if it is the same as the common data bus */
  for (int i = 0; i < MD_TOTAL_REGS; i++) {
    if (map_table[i] == commonDataBus) {
      // PRINT_REG(stdout, i, "CDB_To_retire [MOVE]", map_table[i])
      map_table[i] = NULL;
    }
  }

  /* checks all RS  clears if it is the same as the common data bus */
  for (int i = 0; i < RESERV_FP_SIZE; i++) {
    if (reservFP[i] != NULL) {
      for (int q_i = 0; q_i < 3; q_i++) {
        if (reservFP[i]->Q[q_i] == commonDataBus) {
          reservFP[i]->Q[q_i] = NULL;
        }
      }
    }
  }
  for (int i = 0; i < RESERV_INT_SIZE; i++) {
    if (reservINT[i] != NULL) {
      for (int q_i = 0; q_i < 3; q_i++) {
        if (reservINT[i]->Q[q_i] == commonDataBus) {
          reservINT[i]->Q[q_i] = NULL;
        }
      }
    }
  }

  /* clear CDB */
  commonDataBus = NULL;
  return;
  /* ECE552 Assignment 3 - END CODE */
}

/*
 * Description:
 * 	Moves an instruction from the execution stage to common data bus (if
 * possible) Inputs: current_cycle: the cycle we are at Returns: None
 */
void execute_To_CDB(int current_cycle) {
  /* ECE552 Assignment 3 - BEGIN  CODE */
  /* goes through each functional unit if CDB is available (should be always
   * available) move the oldest instruction that finishes executing into the
   * CDB */
  instruction_t* e_instr = NULL;
  /* goes through the integer FUs first */
  for (int i = 0; i < FU_INT_SIZE; i++) {
    /* if the entry is valid */
    if (fuINT[i] != NULL) {
      /* if the entry can leave execute by the next cycle */
      if (current_cycle >= fuINT[i]->tom_execute_cycle + FU_INT_LATENCY) {
        /* check if this instruction writes to CBD, if it doesn't clear the
         * entry otherwise take the oldest instruction in FU */
        if (!WRITES_CDB(fuINT[i]->op)) {
          /* bypass CDB if the entry can leave and clears rs and fu*/
          for (int rs_i = 0; rs_i < RESERV_INT_SIZE; rs_i++) {
            if (reservINT[rs_i] == fuINT[i]) {
              reservINT[rs_i] = NULL;
              continue;
            }
          }
          fuINT[i] = NULL;
        } else if (e_instr == NULL) {
          e_instr = fuINT[i];
        } else if (e_instr->index > fuINT[i]->index) {
          e_instr = fuINT[i];
        }
      }
    }
  }
  /* then the fp units */
  for (int i = 0; i < FU_FP_SIZE; i++) {
    /* if the entry is valid */
    if (fuFP[i] != NULL) {
      /* if the entry can leave execute by the next cycle */
      if (current_cycle >= fuFP[i]->tom_execute_cycle + FU_FP_LATENCY) {
        /* check if this instruction writes to CBD, if it doesn't clear the
         * entry otherwise take the oldest instruction in FU */
        if (!WRITES_CDB(fuFP[i]->op)) {
          /* bypass CDB if the entry can leave and clears rs and fu*/
          for (int rs_i = 0; rs_i < RESERV_FP_SIZE; rs_i++) {
            if (reservFP[rs_i] == fuFP[i]) {
              reservFP[rs_i] = NULL;
              continue;
            }
          }
          fuFP[i] = NULL;
        } else if (e_instr == NULL) {
          e_instr = fuFP[i];
        } else if (e_instr->index > fuFP[i]->index) {
          e_instr = fuFP[i];
        }
      }
    }
  }
  /* bypass next step if no instruction can leave execute */
  if (e_instr == NULL) {
    return;
  }
  /* clears RS and FU entry */
  for (int i = 0; i < FU_FP_SIZE; i++) {
    if (fuFP[i] == e_instr) {
      fuFP[i] = NULL;
    }
  }
  for (int i = 0; i < FU_INT_SIZE; i++) {
    if (fuINT[i] == e_instr) {
      fuINT[i] = NULL;
    }
  }
  for (int i = 0; i < RESERV_FP_SIZE; i++) {
    if (reservFP[i] == e_instr) {
      reservFP[i] = NULL;
    }
  }
  for (int i = 0; i < RESERV_INT_SIZE; i++) {
    if (reservINT[i] == e_instr) {
      reservINT[i] = NULL;
    }
  }
  /* move the entry into CDB */
  commonDataBus = e_instr;
  e_instr->tom_cdb_cycle = current_cycle;
  /* ECE552 Assignment 3 - END  CODE */
}
/* ECE552 Assignment 3 - BEGIN  CODE */
/*
 * Description:
 * Determines if the instruction in question can be moved into execute
 * Inputs:
 * 	instr: the instruction in RS
 * Returns:
 * 	1 if it can, 0 if it can't
 */
bool canExecute(instruction_t* instr) {
  /* is already executing*/
  if (instr->tom_execute_cycle != -1) {
    return 0;
  }
  /* needs to wait for depedencies */
  for (int i = 0; i < 3; i++) {
    if (instr->Q[i] != NULL) {
      return 0;
    }
  }
  return 1;
}
/* ECE552 Assignment 3 - END  CODE */

/*
 * Description:
 * 	Moves instruction(s) from the issue to the execute stage (if possible).
 * We prioritize old instructions (in program order) over new ones, if they
 * both contend for the same functional unit. All RAW dependences need to
 * have been resolved with stalls before an instruction enters execute.
 * Inputs: current_cycle: the cycle we are at Returns: None
 */
void issue_To_execute(int current_cycle) {
  /* ECE552 Assignment 3 - BEGIN  CODE */
  /* check for functional unit availability
   * if a FU is availble, move the oldest instruction in the RS into the
   * execute stage */
  instruction_t* i_instr = NULL;
  /* check INT FU */
  /* loops over FUs */
  for (int fu_i = 0; fu_i < FU_INT_SIZE; fu_i++) {
    /* if FU is unoccupied */
    if (fuINT[fu_i] == NULL) {
      /* loop through the reservation stations */
      for (int rs_i = 0; rs_i < RESERV_INT_SIZE; rs_i++) {
        /* if the reservation station is not empty */
        if (reservINT[rs_i] != NULL) {
          /* the RS entry must not already be in execute and it should not have
           * any dependencies waiting to be resolved */
          if (canExecute(reservINT[rs_i])) {
            /* take the oldest instruction in RS */
            if (i_instr == NULL) {
              i_instr = reservINT[rs_i];
            } else if (i_instr->index > reservINT[rs_i]->index) {
              i_instr = reservINT[rs_i];
            }
          }
        }
      }
      /* if an instruction is selected */
      if (i_instr != NULL) {
        // PRINT_INST(stdout, i_instr, "issue_To_execute", current_cycle);
        /* move instruction into functional unit */
        fuINT[fu_i] = i_instr;
        /* set the cycle */
        i_instr->tom_execute_cycle = current_cycle;
        /* reset i_instr */
        i_instr = NULL;
      }
    } else {
      // PRINT_INST(stdout, fuINT[fu_i], "fuINT", current_cycle);
    }
  }
  /* check Float FUs */
  for (int fu_i = 0; fu_i < FU_FP_SIZE; fu_i++) {
    /* if FU is unoccupied */
    if (fuFP[fu_i] == NULL) {
      /* loop through the reservation stations */
      for (int rs_i = 0; rs_i < RESERV_FP_SIZE; rs_i++) {
        /* if the reservation station is not empty */
        if (reservFP[rs_i] != NULL) {
          /* the RS entry must be able to execute */
          if (canExecute(reservFP[rs_i])) {
            /* take the oldest instruction in RS */
            if (i_instr == NULL) {
              i_instr = reservFP[rs_i];
            } else if (i_instr->index > reservFP[rs_i]->index) {
              i_instr = reservFP[rs_i];
            }
          }
        }
      }
      /* if an instruction is selected */
      if (i_instr != NULL) {
        // PRINT_INST(stdout, i_instr, "issue_To_execute", current_cycle);
        /* move instruction into functional unit */
        fuFP[fu_i] = i_instr;
        /* set the cycle */
        i_instr->tom_execute_cycle = current_cycle;
        /* reset i_instr */
        i_instr = NULL;
      }
    }
  }
  return;
  /* ECE552 Assignment 3 - END  CODE */
}

/*
 * Description:
 * 	Moves instruction(s) from the dispatch stage to the issue stage
 * Inputs:
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void dispatch_To_issue(int current_cycle) {
  /* ECE552 Assignment 3 - BEGIN  CODE */
  /* checks for instructions that can be moved from dispatch into issue*/
  if (instr_queue_size <= 0) {
    /*do nothing if there are no instructions to move*/
    return;
  }
  /* grab the current instruction head */
  instruction_t* d_instr = instr_queue[instr_queue_head];
  /* move the instruction into issue if RS is available */
  int reg = 0;
  int i = 0;
  /* check which RS should be used */
  if (USES_INT_FU(d_instr->op)) {
    /* find first INT RS */
    while (i < RESERV_INT_SIZE) {
      if (reservINT[i] == NULL) {
        break;
      }
      i++;
    }
    /* no INT RS available -> stall */
    if (i >= RESERV_INT_SIZE) {
      return;
    }
    /* otherwise move instruction into RS */
    reservINT[i] = d_instr;
  } else if (USES_FP_FU(d_instr->op)) {
    /* find first FP reservation station */
    while (i < RESERV_FP_SIZE) {
      if (reservFP[i] == NULL) {
        break;
      }
      i++;
    }
    /* no FP RS available -> stall */
    if (i >= RESERV_FP_SIZE) {
      return;
    }
    /* otherwise move instruction into RS */
    reservFP[i] = d_instr;
  } else if (IS_COND_CTRL(d_instr->op) || IS_UNCOND_CTRL(d_instr->op)) {
    /* do nothing if CTRL */
  }

  // PRINT_INST(stdout, d_instr, "dispatch_To_issue", current_cycle);
  /* set cycle the intruction enters dispatch */
  d_instr->tom_issue_cycle = current_cycle;
  /* populate the Q array with values, if NULL -> value available in register
   * otherwise store the instruction pointer */
  for (i = 0; i < 3; i++) {
    reg = d_instr->r_in[i];
    // NOTE: add the check to make sure no fake dependency created!
    if (reg < 0 || reg >= MD_TOTAL_REGS) continue;
    d_instr->Q[i] = map_table[reg];
    if (map_table[reg] != NULL) {
      // PRINT_REG(stdout, reg, "dispatch_To_issue [ADD_1]", map_table[reg])
    }
  }
  /* populate the map_table with the registers this instruction writes to
   * iff it writes to CBD */
  if (WRITES_CDB(d_instr->op)) {
    for (i = 0; i < 2; i++) {
      reg = d_instr->r_out[i];
      // NOTE: somehow r_out[1] is -1 which added fake dependencies!
      if (reg < 0 || reg >= MD_TOTAL_REGS) continue;
      map_table[reg] = d_instr;
      // PRINT_REG(stdout, reg, "dispatch_To_issue [ADD_2]", map_table[reg])
    }
  }
  /* pops head from queue*/
  instr_queue_size--;
  instr_queue_head++;
  /* Resolve wrap around */
  if (instr_queue_head == INSTR_QUEUE_SIZE) {
    instr_queue_head = 0;
  }

  return;
  /* ECE552 Assignment 3 - END  CODE */
}

/*
 * Description:
 * 	Grabs an instruction from the instruction trace (if possible)
 * Inputs:
 *      trace: instruction trace with all the instructions executed
 * Returns:
 * 	None
 */
void fetch(instruction_trace_t* trace) {
  /* ECE552 Assignment 3 - BEGIN  CODE */

  /* Checks if the queue is full if it is bypass fetch/stall until the queue
   * has space*/
  if (instr_queue_size == INSTR_QUEUE_SIZE || fetch_index > sim_num_insn) {
    return;
  }

  /* fetch *1* instruction at a time
   * ignore trap instructions by fetching until a non trap instruction */
  while (fetch_index < sim_num_insn) {
    /* first instruction is invalid, this skips over index 0 */
    fetch_index++;
    instr_queue[instr_queue_tail] = get_instr(trace, fetch_index);
    // if not a trap add to queue and return
    if (!IS_TRAP(instr_queue[instr_queue_tail]->op)) {
      /* initialises the tom cycle tracker */
      instr_queue[instr_queue_tail]->tom_cdb_cycle = -1;
      instr_queue[instr_queue_tail]->tom_dispatch_cycle = -1;
      instr_queue[instr_queue_tail]->tom_execute_cycle = -1;
      instr_queue[instr_queue_tail]->tom_issue_cycle = -1;

      // PRINT_INST(stdout, instr_queue[instr_queue_tail], "fetch_To_dispatch", current_cycle);

      // Update the instruction queue size
      instr_queue_size++;
      return;
    }
  }

  /* ECE552 Assignment 3 - END  CODE */
}

/*
 * Description:
 * 	Calls fetch and dispatches an instruction at the same cycle (if
 * possible) Inputs: trace: instruction trace with all the instructions
 * executed current_cycle: the cycle we are at Returns: None
 */
void fetch_To_dispatch(instruction_trace_t* trace, int current_cycle) {
  fetch(trace);

  /* ECE552 Assignment 3 - BEGIN  CODE */
  /* Checks if a new instruction has been fetched*/
  if (instr_queue[instr_queue_tail] &&
      instr_queue[instr_queue_tail]->tom_dispatch_cycle == -1) {
    /* set the tom_dispatch cycle */
    instr_queue[instr_queue_tail]->tom_dispatch_cycle = current_cycle;

    /* Update the queue tail index */
    instr_queue_tail++;

    /* Resolve wrap around */
    if (instr_queue_tail == INSTR_QUEUE_SIZE) {
      instr_queue_tail = 0;
    }
  }
  /* ECE552 Assignment 3 - END  CODE */
}

/*
 * Description:
 * 	Performs a cycle-by-cycle simulation of the 4-stage pipeline
 * Inputs:
 *      trace: instruction trace with all the instructions executed
 * Returns:
 * 	The total number of cycles it takes to execute the instructions.
 * Extra Notes:
 * 	sim_num_insn: the number of instructions in the trace
 */
counter_t runTomasulo(instruction_trace_t* trace) {
  // initialize instruction queue
  int i;
  for (i = 0; i < INSTR_QUEUE_SIZE; i++) {
    instr_queue[i] = NULL;
  }

  // initialize reservation stations
  for (i = 0; i < RESERV_INT_SIZE; i++) {
    reservINT[i] = NULL;
  }

  for (i = 0; i < RESERV_FP_SIZE; i++) {
    reservFP[i] = NULL;
  }

  // initialize functional units
  for (i = 0; i < FU_INT_SIZE; i++) {
    fuINT[i] = NULL;
  }

  for (i = 0; i < FU_FP_SIZE; i++) {
    fuFP[i] = NULL;
  }

  // initialize map_table to no producers
  int reg;
  for (reg = 0; reg < MD_TOTAL_REGS; reg++) {
    map_table[reg] = NULL;
  }

  int cycle = 1;
  // the current instruction being fetched
  while (true) {
    /* ECE552: YOUR CODE GOES HERE */

    /* ECE552 Assignment 3 - BEGIN  CODE */

    /* CBD to Retire */
    /* This executes first to free up CBD for execute to CBD */
    CDB_To_retire(cycle);

    /* Execute to CBD */
    /* This executes before issue to execute and dispatch to issue so we know
     * which RS and FU will be freed up by the next cycle */
    execute_To_CDB(cycle);

    /* Issue to Execute */
    /* this runs before issue to execute, so that the instructin put into
     * dispatch this cycle doesn't enter execute until the next cycle */
    issue_To_execute(cycle);

    /* Dispatch to Issue */
    /* this runs before fetch to dispatch so that the insturctions dispatched
     * doesn't enter issue until the next cycle if a RS is available */
    dispatch_To_issue(cycle);

    /* Fetch / Dispatch */
    fetch_To_dispatch(trace, cycle);

    /* ECE552 Assignment 3 - END CODE */
    cycle++;
    if (is_simulation_done(sim_num_insn)) break;
  }

  return cycle;
}
