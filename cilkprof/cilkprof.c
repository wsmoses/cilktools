#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
/* #define _POSIX_C_SOURCE = 200112L */
/* #define _POSIX_C_SOURCE = 200809L */
#include <stdbool.h>
#include <inttypes.h>
#include <assert.h>

#include <float.h>
#include <unistd.h>
#include <sys/types.h>

#include <cilktool.h>
#include "cilkprof_stack.h"
#include "util.h"

#ifndef SERIAL_TOOL
#define SERIAL_TOOL 1
#endif

#ifndef OLD_PRINTOUT 
#define OLD_PRINTOUT 0
#endif

#ifndef COMPUTE_STRAND_DATA
#define COMPUTE_STRAND_DATA 0
#endif

#ifndef TRACE_CALLS
#define TRACE_CALLS 0
#endif

#if SERIAL_TOOL
#define GET_STACK(ex) ex
#else
#define GET_STACK(ex) REDUCER_VIEW(ex)
#include "cilkprof_stack_reducer.h"
#endif

#include <libgen.h>


// TB: Adjusted so I can terminate WHEN_TRACE_CALLS() with semicolons.
// Emacs gets confused about tabbing otherwise.
#if TRACE_CALLS
#define WHEN_TRACE_CALLS(ex) do { ex } while (0)
#else
#define WHEN_TRACE_CALLS(ex) do {} while (0)
#endif

/*************************************************************************/
/**
 * Data structures for tracking work and span.
 */


#if SERIAL_TOOL
static cilkprof_stack_t ctx_stack;
#else
static CILK_C_DECLARE_REDUCER(cilkprof_stack_t) ctx_stack =
  CILK_C_INIT_REDUCER(cilkprof_stack_t,
		      reduce_cilkprof_stack,
		      identity_cilkprof_stack,
		      destroy_cilkprof_stack,
		      {NULL});
#endif

static bool TOOL_INITIALIZED = false;
static bool TOOL_PRINTED = false;

/*************************************************************************/
/**
 * Helper methods.
 */

static inline void initialize_tool(cilkprof_stack_t *stack) {
#if SERIAL_TOOL
  // This is a serial tool
  ensure_serial_tool();
#else
  // probably need to register the reducer here as well.
  CILK_C_REGISTER_REDUCER(ctx_stack);
#endif
  cilkprof_stack_init(stack, MAIN);
  TOOL_INITIALIZED = true;
  TOOL_PRINTED = false;
}

__attribute__((always_inline))
void begin_strand(cilkprof_stack_t *stack) {
  start_strand(&(stack->strand_ruler));
}

__attribute__((always_inline))
void measure_and_add_strand_length(cilkprof_stack_t *stack) {
  // Measure strand length
  uint64_t strand_len = measure_strand_length(&(stack->strand_ruler));
  assert(NULL != stack->bot);

  // Accumulate strand length
  stack->bot->local_wrk += strand_len;
  stack->bot->local_contin += strand_len;
  stack->bot->running_wrk += strand_len;
  stack->bot->contin_spn += strand_len;

#if COMPUTE_STRAND_DATA
  // Add strand length to strand_wrk and strand_contin tables
  /* fprintf(stderr, "start %lx, end %lx\n", stack->strand_start, stack->strand_end); */
  bool add_success = add_to_strand_hashtable(&(stack->strand_wrk_table),
                                             stack->strand_start,
                                             stack->strand_end,
                                             strand_len);
  assert(add_success);
  add_success = add_to_strand_hashtable(&(stack->bot->strand_contin_table),
                                        stack->strand_start,
                                        stack->strand_end,
                                        strand_len);
  assert(add_success);
#endif
}

/*************************************************************************/

void cilk_tool_init(void) {
  // Do the initialization only if it hasn't been done. 
  // It could have been done if we instrument C functions, and the user 
  // separately calls cilk_tool_init in the main function.
  if(!TOOL_INITIALIZED) {
    WHEN_TRACE_CALLS( fprintf(stderr, "cilk_tool_init() [ret %p]\n",
                              __builtin_extract_return_addr(__builtin_return_address(0))); );

    initialize_tool(&GET_STACK(ctx_stack));

    GET_STACK(ctx_stack).in_user_code = true;

    begin_strand(&(GET_STACK(ctx_stack)));
  }
}

/* Cleaningup; note that these cleanup may not be performed if
 * the user did not include cilk_tool_destroy in its main function and the
 * program is not compiled with -fcilktool_instr_c.
 */
void cilk_tool_destroy(void) {
  // Do the destroy only if it hasn't been done. 
  // It could have been done if we instrument C functions, and the user 
  // separately calls cilk_tool_destroy in the main function.
  if(TOOL_INITIALIZED) {
    WHEN_TRACE_CALLS( fprintf(stderr, "cilk_tool_destroy() [ret %p]\n",
                              __builtin_extract_return_addr(__builtin_return_address(0))); );

    cilkprof_stack_t *stack = &GET_STACK(ctx_stack);
    // Print the output, if we haven't done so already
    if (!TOOL_PRINTED)
      cilk_tool_print();

    // Pop the stack
    cilkprof_stack_frame_t *old_bottom = cilkprof_stack_pop(stack);

    assert(old_bottom && MAIN == old_bottom->func_type);

#if !SERIAL_TOOL
    CILK_C_UNREGISTER_REDUCER(ctx_stack);
#endif
    free_cc_hashtable(stack->wrk_table);
    free_cc_hashtable(old_bottom->prefix_table);
    free_cc_hashtable(old_bottom->lchild_table);
    free_cc_hashtable(old_bottom->contin_table);
    free_strand_hashtable(stack->strand_wrk_table);
    free_strand_hashtable(old_bottom->strand_prefix_table);
    free_strand_hashtable(old_bottom->strand_lchild_table);
    free_strand_hashtable(old_bottom->strand_contin_table);
    free(old_bottom);

    TOOL_INITIALIZED = false;
  }
}


void cilk_tool_print(void) {
  FILE *fout;

  WHEN_TRACE_CALLS( fprintf(stderr, "cilk_tool_print()\n"); );

  assert(TOOL_INITIALIZED);

  cilkprof_stack_t *stack;
  stack = &GET_STACK(ctx_stack);

  assert(NULL != stack->bot);
  assert(MAIN == stack->bot->func_type);

  uint64_t span = stack->bot->prefix_spn + stack->bot->contin_spn;

  add_cc_hashtables(&(stack->bot->prefix_table), &(stack->bot->contin_table));
  clear_cc_hashtable(stack->bot->contin_table);

  flush_cc_hashtable(&(stack->bot->prefix_table));

  cc_hashtable_t* span_table = stack->bot->prefix_table;
  fprintf(stderr, 
          "span_table->list_size = %d, span_table->table_size = %d, span_table->lg_capacity = %d\n",
  	  span_table->list_size, span_table->table_size, span_table->lg_capacity);


  uint64_t work = stack->bot->running_wrk;
  flush_cc_hashtable(&(stack->wrk_table));
  cc_hashtable_t* work_table = stack->wrk_table;
  fprintf(stderr, 
          "work_table->list_size = %d, work_table->table_size = %d, work_table->lg_capacity = %d\n",
  	  work_table->list_size, work_table->table_size, work_table->lg_capacity);

  // Read the proc maps list
  read_proc_maps();

  // Open call site CSV
  fout = fopen("cilkprof_cs.csv", "w"); 

  // print the header for the csv file
  /* fprintf(fout, "file, line, call sites (rip), depth, "); */
  fprintf(fout, "file, line, call sites (rip), function type, ");
  fprintf(fout, "work on work, span on work, parallelism on work, count on work, ");
  fprintf(fout, "top work on work, top span on work, top parallelism on work, top count on work, ");
  fprintf(fout, "local work on work, local span on work, local parallelism on work, local count on work, ");
  fprintf(fout, "work on span, span on span, parallelism on span, count on span, ");
  fprintf(fout, "top work on span, top span on span, top parallelism on span, top count on span, ");
  fprintf(fout, "local work on span, local span on span, local parallelism on span, local count on span \n");

  // Parse tables
  size_t span_table_entries_read = 0;
  for (size_t i = 0; i < (1 << work_table->lg_capacity); ++i) {
    cc_hashtable_entry_t *entry = &(work_table->entries[i]);
    if (!empty_cc_entry_p(entry)) {
      uint64_t wrk_wrk = entry->wrk;
      uint64_t spn_wrk = entry->spn;
      double par_wrk = (double)wrk_wrk/(double)spn_wrk;
      uint64_t cnt_wrk = entry->count;

      uint64_t t_wrk_wrk = entry->top_wrk;
      uint64_t t_spn_wrk = entry->top_spn;
      double t_par_wrk = (double)t_wrk_wrk/(double)t_spn_wrk;
      uint64_t t_cnt_wrk = entry->top_count;

      uint64_t l_wrk_wrk = entry->local_wrk;
      uint64_t l_spn_wrk = entry->local_spn;
      double l_par_wrk = (double)l_wrk_wrk/(double)l_spn_wrk;
      uint64_t l_cnt_wrk = entry->local_count;

      uint64_t wrk_spn = 0;
      uint64_t spn_spn = 0;
      double par_spn = DBL_MAX;
      uint64_t cnt_spn = 0;

      uint64_t t_wrk_spn = 0;
      uint64_t t_spn_spn = 0;
      double t_par_spn = DBL_MAX;
      uint64_t t_cnt_spn = 0;

      uint64_t l_wrk_spn = 0;
      uint64_t l_spn_spn = 0;
      double l_par_spn = DBL_MAX;
      uint64_t l_cnt_spn = 0;

      cc_hashtable_entry_t *st_entry = 
          get_cc_hashtable_entry_const(entry->rip, span_table);
      if(st_entry && !empty_cc_entry_p(st_entry)) {
        /* assert(st_entry->depth >= entry->depth); */
        ++span_table_entries_read;
        /* if((INT32_MAX == st_entry->depth && INT32_MAX == entry->depth) || */
        /*    (INT32_MAX > st_entry->depth && INT32_MAX > entry->depth)) { */
        /* if(st_entry->depth == entry->depth) { */
          wrk_spn = st_entry->wrk;
          spn_spn = st_entry->spn;
          par_spn = (double)wrk_spn / (double)spn_spn;
          cnt_spn = st_entry->count;
        /* } */
        t_wrk_spn = st_entry->top_wrk;
        t_spn_spn = st_entry->top_spn;
        t_par_spn = (double)t_wrk_spn / (double)t_spn_spn;
        t_cnt_spn = st_entry->top_count;

        l_wrk_spn = st_entry->local_wrk;
        l_spn_spn = st_entry->local_spn;
        l_par_spn = (double)l_wrk_spn / (double)l_spn_spn;
        l_cnt_spn = st_entry->local_count;
      }

#if OLD_PRINTOUT
      fprintf(stdout, "%lx:%d ", rip2cc(entry->rip), entry->depth);
      print_addr(rip2cc(entry->rip));
      fprintf(stdout, " %lu %lu %lu %lu\n",
	      wrk_wrk, spn_wrk, wrk_spn, spn_spn);
#endif
      int line = 0; 
      char *fstr = NULL;
      uint64_t addr = rip2cc(entry->rip);

      // get_info_on_inst_addr returns a char array from some system call that
      // needs to get freed by the user after we are done with the info
      char *line_to_free = get_info_on_inst_addr(addr, &line, &fstr);
      char *file = basename(fstr);
      /* fprintf(fout, "\"%s\", %d, 0x%lx, %d, ", file, line, addr, entry->depth); */
      fprintf(fout, "\"%s\", %d, 0x%lx, ", file, line, addr);
      if (entry->is_recursive) {  // recursive function
        fprintf(fout, "%s %s, ", FunctionType_str[entry->func_type], "recursive");
      } else {
        fprintf(fout, "%s, ", FunctionType_str[entry->func_type]);
      }
      fprintf(fout, "%lu, %lu, %g, %lu, %lu, %lu, %g, %lu, %lu, %lu, %g, %lu, ", 
              wrk_wrk, spn_wrk, par_wrk, cnt_wrk,
              t_wrk_wrk, t_spn_wrk, t_par_wrk, t_cnt_wrk,
              l_wrk_wrk, l_spn_wrk, l_par_wrk, l_cnt_wrk);
      fprintf(fout, "%lu, %lu, %g, %lu, %lu, %lu, %g, %lu, %lu, %lu, %g, %lu\n", 
              wrk_spn, spn_spn, par_spn, cnt_spn,
              t_wrk_spn, t_spn_spn, t_par_spn, t_cnt_spn,
              l_wrk_spn, l_spn_spn, l_par_spn, l_cnt_spn);
      if(line_to_free) free(line_to_free);
    }
  }
  fclose(fout);

  assert(span_table_entries_read == span_table->table_size);

#if COMPUTE_STRAND_DATA
  // Strand tables
  add_strand_hashtables(&(stack->bot->strand_prefix_table), &(stack->bot->strand_contin_table));
  clear_strand_hashtable(stack->bot->strand_contin_table);

  flush_strand_hashtable(&(stack->bot->strand_prefix_table));

  strand_hashtable_t* strand_span_table = stack->bot->strand_prefix_table;
  fprintf(stderr, 
          "strand_span_table->list_size = %d, strand_span_table->table_size = %d, strand_span_table->lg_capacity = %d\n",
  	  strand_span_table->list_size, strand_span_table->table_size, strand_span_table->lg_capacity);


  flush_strand_hashtable(&(stack->strand_wrk_table));
  strand_hashtable_t* strand_work_table = stack->strand_wrk_table;
  fprintf(stderr, 
          "strand_work_table->list_size = %d, strand_work_table->table_size = %d, strand_work_table->lg_capacity = %d\n",
  	  strand_work_table->list_size, strand_work_table->table_size, strand_work_table->lg_capacity);

  // Open strand CSV
  fout = fopen("cilkprof_strand.csv", "w"); 

  // print the header for the csv file
  fprintf(fout, "start file, start line, start rip, end file, end line, end rip, ");
  fprintf(fout, "work on work, count on work, ");
  fprintf(fout, "work on span, count on span \n");

  // Parse tables
  span_table_entries_read = 0;
  for (size_t i = 0; i < (1 << strand_work_table->lg_capacity); ++i) {
    strand_hashtable_entry_t *entry = &(strand_work_table->entries[i]);
    /* fprintf(stderr, "entry->start %lx, entry->end %lx\n", */
    /*         entry->start, entry->end); */
    if (!empty_strand_entry_p(entry)) {
      uint64_t wrk_wrk = entry->wrk;
      uint64_t on_wrk_cnt = entry->count;
      uint64_t wrk_spn = 0;
      uint64_t on_spn_cnt = 0;

      strand_hashtable_entry_t *st_entry = 
          get_strand_hashtable_entry_const(entry->start, entry->end, strand_span_table);
      if(st_entry && !empty_strand_entry_p(st_entry)) {
	  ++span_table_entries_read;
          wrk_spn = st_entry->wrk;
          on_spn_cnt = st_entry->count;
      }

#if OLD_PRINTOUT
      fprintf(stdout, "%lx:%lx ", rip2cc(entry->start), rip2cc(entry->end));
      fprintf(stdout, " %lu %lu\n",
	      wrk_wrk, wrk_spn);
#endif
      int line = 0; 
      char *fstr = NULL;
      uint64_t start_addr = rip2cc(entry->start);
      uint64_t end_addr = rip2cc(entry->end);

      // get_info_on_inst_addr returns a char array from some system call that
      // needs to get freed by the user after we are done with the info
      char *line_to_free = get_info_on_inst_addr(start_addr, &line, &fstr);
      char *file = basename(fstr);
      fprintf(fout, "\"%s\", %d, 0x%lx, ", file, line, start_addr);
      if(line_to_free) free(line_to_free);
      line_to_free = get_info_on_inst_addr(end_addr, &line, &fstr);
      file = basename(fstr);
      fprintf(fout, "\"%s\", %d, 0x%lx, ", file, line, end_addr);
      if(line_to_free) free(line_to_free);
      fprintf(fout, "%lu, %lu, %lu, %lu\n", 
              wrk_wrk, on_wrk_cnt, wrk_spn, on_spn_cnt);
    }
  }
  fclose(fout);

  assert(span_table_entries_read == strand_span_table->table_size);
#endif  // COMPUTE_STRAND_DATA

  fprintf(stderr, "work = %fs, span = %fs, parallelism = %f\n",
	  work / (1000000000.0),
	  span / (1000000000.0),
	  work / (float)span);

  /*
  fprintf(stderr, "%ld read, %d size\n", span_table_entries_read, span_table->table_size);
  fprintf(stderr, "Dumping span table:\n");
  for (size_t j = 0; j < (1 << span_table->lg_capacity); ++j) {
    cc_hashtable_entry_t *st_entry = &(span_table->entries[j]);
    if (empty_cc_entry_p(st_entry)) {
      continue;
    }
    fprintf(stderr, "entry %zu: rip %lx, depth %d\n", j, rip2cc(st_entry->rip), st_entry->depth);
  } */

  // Free the proc maps list
  mapping_list_el_t *map_lst_el = maps.head;
  mapping_list_el_t *next_map_lst_el;
  while (NULL != map_lst_el) {
    next_map_lst_el = map_lst_el->next;
    free(map_lst_el);
    map_lst_el = next_map_lst_el;
  }
  maps.head = NULL;
  maps.tail = NULL;

  TOOL_PRINTED = true;
}


/*************************************************************************/
/**
 * Hooks into runtime system.
 */

void cilk_enter_begin(__cilkrts_stack_frame *sf, void* this_fn, void* rip)
{
  WHEN_TRACE_CALLS( fprintf(stderr, "cilk_enter_begin(%p, %p) [ret %p]\n", sf, rip,
                            __builtin_extract_return_addr(__builtin_return_address(0))); );

  /* fprintf(stderr, "worker %d entering %p\n", __cilkrts_get_worker_number(), sf); */
  cilkprof_stack_t *stack = &(GET_STACK(ctx_stack));

  if (!TOOL_INITIALIZED) {
    initialize_tool(&(ctx_stack));

  } else {
    stack = &(GET_STACK(ctx_stack));

#if COMPUTE_STRAND_DATA
    // Prologue disabled
    stack->strand_end
        = (uintptr_t)__builtin_extract_return_addr(__builtin_return_address(0));
#endif
    measure_and_add_strand_length(stack);

    stack->in_user_code = false;
  }

  // Push new frame onto the stack
  cilkprof_stack_push(stack, SPAWNER);

  stack->bot->rip = (uintptr_t)__builtin_extract_return_addr(rip);
  stack->bot->function = (uintptr_t)this_fn;

  enter_call_site(&(stack->unique_call_sites),
                  stack->bot->rip, stack->bot->function,
                  stack->bot->depth);
}


void cilk_enter_helper_begin(__cilkrts_stack_frame *sf, void *this_fn, void *rip)
{
  cilkprof_stack_t *stack = &(GET_STACK(ctx_stack));

  WHEN_TRACE_CALLS( fprintf(stderr, "cilk_enter_helper_begin(%p, %p) [ret %p]\n", sf, rip,
                            __builtin_extract_return_addr(__builtin_return_address(0))); );

  // We should have passed spawn_or_continue(0) to get here.
  assert(stack->in_user_code);
#if COMPUTE_STRAND_DATA
  // Prologue disabled
  stack->strand_end
      = (uintptr_t)__builtin_extract_return_addr(__builtin_return_address(0));
#endif
  measure_and_add_strand_length(stack);
  stack->in_user_code = false;

  // Push new frame onto the stack
  cilkprof_stack_push(stack, HELPER);

  stack->bot->rip = (uintptr_t)__builtin_extract_return_addr(rip);
  stack->bot->function = (uintptr_t)this_fn;

  enter_call_site(&(stack->unique_call_sites),
                  stack->bot->rip, stack->bot->function,
                  stack->bot->depth);
}

void cilk_enter_end(__cilkrts_stack_frame *sf, void *rsp)
{
  cilkprof_stack_t *stack = &(GET_STACK(ctx_stack));

  if (SPAWNER == stack->bot->func_type) {
    WHEN_TRACE_CALLS( fprintf(stderr, "cilk_enter_end(%p, %p) from SPAWNER [ret %p]\n", sf, rsp,
                              __builtin_extract_return_addr(__builtin_return_address(0))); );
  } else {
    WHEN_TRACE_CALLS( fprintf(stderr, "cilk_enter_end(%p, %p) from HELPER [ret %p]\n", sf, rsp,
                              __builtin_extract_return_addr(__builtin_return_address(0))); );
  }
  assert(!(stack->in_user_code));

  stack->in_user_code = true;

#if COMPUTE_STRAND_DATA
  stack->strand_start
      = (uintptr_t)__builtin_extract_return_addr(__builtin_return_address(0));
#endif
  begin_strand(stack);
}

void cilk_tool_c_function_enter(void *this_fn, void *rip)
{
  cilkprof_stack_t *stack = &(GET_STACK(ctx_stack));

  /* WHEN_TRACE_CALLS( fprintf(stderr, "c_function_enter(%p) [ret %p]\n", rip,
     __builtin_extract_return_addr(__builtin_return_address(0))); ); */

  if(!TOOL_INITIALIZED) { // We are entering main.
    cilk_tool_init(); // this will push the frame for MAIN and do a gettime
    stack->bot->rip = (uintptr_t)__builtin_extract_return_addr(rip);
    stack->bot->function = (uintptr_t)this_fn;
    enter_call_site(&(stack->unique_call_sites),
                    stack->bot->rip, stack->bot->function,
                    stack->bot->depth);
#if COMPUTE_STRAND_DATA
    stack->strand_start
        = (uintptr_t)__builtin_extract_return_addr(__builtin_return_address(0));
#endif
  } else {
    if (!stack->in_user_code) {
      WHEN_TRACE_CALLS( fprintf(stderr, "c_function_enter(%p) [ret %p]\n", rip,
                                __builtin_extract_return_addr(__builtin_return_address(0))); );
    }
    assert(stack->in_user_code);
#if COMPUTE_STRAND_DATA
    stack->strand_end
        = (uintptr_t)__builtin_extract_return_addr(__builtin_return_address(0));
#endif
    measure_and_add_strand_length(stack);

    // Push new frame for this C function onto the stack
    cilkprof_stack_push(stack, C_FUNCTION);
    stack->bot->rip = (uintptr_t)__builtin_extract_return_addr(rip);
    stack->bot->function = (uintptr_t)this_fn;
    enter_call_site(&(stack->unique_call_sites),
                    stack->bot->rip, stack->bot->function,
                    stack->bot->depth);

#if COMPUTE_STRAND_DATA
    stack->strand_start
        = (uintptr_t)__builtin_extract_return_addr(__builtin_return_address(0));
#endif
    /* the stop time is also the start time of this function */
    // stack->start = stack->stop; /* TB: Want to exclude the length
    // (e.g. time or instruction count) of this function */
    begin_strand(stack);
  }
}

void cilk_tool_c_function_leave(void *rip)
{
  WHEN_TRACE_CALLS( fprintf(stderr, "c_function_leave(%p) [ret %p]\n", rip,
     __builtin_extract_return_addr(__builtin_return_address(0))); );

  cilkprof_stack_t *stack = &(GET_STACK(ctx_stack));

  if(stack->bot && MAIN == stack->bot->func_type) {
    exit_call_site(&(stack->unique_call_sites),
                   stack->bot->rip, stack->bot->function,
                   stack->bot->depth);
    
    cilk_tool_destroy();
  }
  if(!TOOL_INITIALIZED) {
    // either user code already called cilk_tool_destroy, or we are leaving
    // main; in either case, nothing to do here;
    return;
  }

  bool add_success;
  cilkprof_stack_frame_t *old_bottom;

  assert(stack->in_user_code);
  // stop the timer and attribute the elapsed time to this returning
  // function
#if COMPUTE_STRAND_DATA
  stack->strand_end
      = (uintptr_t)__builtin_extract_return_addr(__builtin_return_address(0));
#endif
  measure_and_add_strand_length(stack);

  assert(NULL != stack->bot->parent);
  // Given this is a C function, everything should be accumulated in
  // contin_spn and contin_table, so let's just deposit that into the
  // parent.
  assert(0 == stack->bot->prefix_spn);
  assert(0 == stack->bot->local_spn);
  assert(0 == stack->bot->lchild_spn);
  assert(cc_hashtable_is_empty(stack->bot->prefix_table));
  assert(cc_hashtable_is_empty(stack->bot->lchild_table));
#if COMPUTE_STRAND_DATA
  assert(strand_hashtable_is_empty(stack->bot->strand_prefix_table));
  assert(strand_hashtable_is_empty(stack->bot->strand_lchild_table));
#endif

  // Pop the stack
  old_bottom = cilkprof_stack_pop(stack);
  int32_t min_cs_depth = exit_call_site(&(stack->unique_call_sites),
                                        old_bottom->rip, old_bottom->function,
                                        old_bottom->depth);

  stack->bot->running_wrk += old_bottom->running_wrk;
  stack->bot->contin_spn += old_bottom->contin_spn;
  // Don't add old_bottom's local_wrk or local_spn

  // Update continuation span table
  /* fprintf(stderr, "adding tables\n"); */
  add_cc_hashtables(&(stack->bot->contin_table), &(old_bottom->contin_table));
#if COMPUTE_STRAND_DATA
  add_strand_hashtables(&(stack->bot->strand_contin_table), &(old_bottom->strand_contin_table));
#endif

  InstanceType_t inst_type
      = (RECURSIVE & -(INT32_MAX != min_cs_depth))
      | (TOP & -(!function_on_stack_above(stack->unique_call_sites,
                                          stack->bot->function,
                                          stack->bot->depth)));
  // Update work table
  if (INT32_MAX == min_cs_depth || min_cs_depth == old_bottom->depth) {
    /* fprintf(stderr, "adding to wrk table\n"); */
    add_success = add_to_cc_hashtable(&(stack->wrk_table),
                                      inst_type | RECORD,
                                      old_bottom->func_type,
                                      old_bottom->rip,
                                      old_bottom->running_wrk,
                                      old_bottom->contin_spn,
                                      old_bottom->local_wrk,
                                      old_bottom->local_contin);
    assert(add_success);
    /* fprintf(stderr, "adding to prefix table\n"); */
    add_success = add_to_cc_hashtable(&(stack->bot->contin_table),
                                      inst_type | RECORD,
                                      old_bottom->func_type,
                                      old_bottom->rip,
                                      old_bottom->running_wrk,
                                      old_bottom->contin_spn,
                                      old_bottom->local_wrk,
                                      old_bottom->local_contin);
    assert(add_success);
  } else {
    // Only record the local work and local span
    /* fprintf(stderr, "adding to wrk table\n"); */
    add_success = add_to_cc_hashtable(&(stack->wrk_table),
                                      0,
                                      old_bottom->func_type,
                                      old_bottom->rip,
                                      0,
                                      0,
                                      old_bottom->local_wrk,
                                      old_bottom->local_contin);
    assert(add_success);
    /* fprintf(stderr, "adding to contin table\n"); */
    add_success = add_to_cc_hashtable(&(stack->bot->contin_table),
                                      0,
                                      old_bottom->func_type,
                                      old_bottom->rip,
                                      0,
                                      0,
                                      old_bottom->local_wrk,
                                      old_bottom->local_contin);
    assert(add_success);
  }

/*   bool is_recursive = exit_call_site(&(stack->unique_call_sites), */
/*                                      old_bottom->rip, old_bottom->function, */
/*                                      old_bottom->depth); */
/*   int32_t depth = is_recursive ? old_bottom->depth : INT32_MAX; */

/*   // Update continuation span table */
/*   /\* fprintf(stderr, "adding tables\n"); *\/ */
/*   add_cc_hashtables(&(stack->bot->contin_table), &(old_bottom->contin_table)); */
/* #if COMPUTE_STRAND_DATA */
/*   add_strand_hashtables(&(stack->bot->strand_contin_table), &(old_bottom->strand_contin_table)); */
/* #endif */

/*   // Update work table */
/*   if (!is_recursive || */
/*       !function_on_stack_above(stack->unique_call_sites, */
/*                                stack->bot->function, stack->bot->depth)) { */
/*     /\* fprintf(stderr, "adding to wrk table\n"); *\/ */
/*     add_success = add_to_cc_hashtable(&(stack->wrk_table), */
/*                                       depth, */
/*                                       old_bottom->func_type, */
/*                                       old_bottom->rip, */
/*                                       old_bottom->running_wrk, */
/*                                       old_bottom->contin_spn, */
/*                                       old_bottom->local_wrk, */
/*                                       old_bottom->local_contin); */
/*     assert(add_success); */

/*     /\* fprintf(stderr, "adding to contin table\n"); *\/ */
/*     add_success = add_to_cc_hashtable(&(stack->bot->contin_table), */
/*                                       depth, */
/*                                       old_bottom->func_type, */
/*                                       old_bottom->rip, */
/*                                       old_bottom->running_wrk, */
/*                                       old_bottom->contin_spn, */
/*                                       old_bottom->local_wrk, */
/*                                       old_bottom->local_contin); */
/*     assert(add_success); */
/*   } else { */
/*     /\* fprintf(stderr, "adding to wrk table\n"); *\/ */
/*     add_success = add_to_cc_hashtable(&(stack->wrk_table), */
/*                                       INT32_MAX, */
/*                                       old_bottom->func_type, */
/*                                       old_bottom->rip, */
/*                                       0, */
/*                                       0, */
/*                                       old_bottom->local_wrk, */
/*                                       old_bottom->local_contin); */
/*     assert(add_success); */

/*     /\* fprintf(stderr, "adding to contin table\n"); *\/ */
/*     add_success = add_to_cc_hashtable(&(stack->bot->contin_table), */
/*                                       INT32_MAX, */
/*                                       old_bottom->func_type, */
/*                                       old_bottom->rip, */
/*                                       0, */
/*                                       0, */
/*                                       old_bottom->local_wrk, */
/*                                       old_bottom->local_contin); */
/*     assert(add_success); */
/*   } */

  // clean up
  free(old_bottom->prefix_table);
  free(old_bottom->contin_table);
  free(old_bottom->lchild_table);
  free(old_bottom->strand_prefix_table);
  free(old_bottom->strand_contin_table);
  free(old_bottom->strand_lchild_table);
  free(old_bottom);
#if COMPUTE_STRAND_DATA
  stack->strand_start
      = (uintptr_t)__builtin_extract_return_addr(__builtin_return_address(0));
#endif
  begin_strand(stack);
}

void cilk_spawn_prepare(__cilkrts_stack_frame *sf)
{
  WHEN_TRACE_CALLS( fprintf(stderr, "cilk_spawn_prepare(%p) [ret %p]\n", sf,
                            __builtin_extract_return_addr(__builtin_return_address(0))); );

  // Tool must have been initialized as this is only called in a SPAWNER, and 
  // we would have at least initialized the tool in the first cilk_enter_begin.
  assert(TOOL_INITIALIZED);

  cilkprof_stack_t *stack = &(GET_STACK(ctx_stack));

#if COMPUTE_STRAND_DATA
  stack->strand_end
      = (uintptr_t)__builtin_extract_return_addr(__builtin_return_address(0));
#endif
  measure_and_add_strand_length(stack);

  assert(stack->in_user_code);
  stack->in_user_code = false;
}

// If in_continuation == 0, we just did setjmp and about to call the spawn helper.  
// If in_continuation == 1, we are resuming after setjmp (via longjmp) at the continuation 
// of a spawn statement; note that this is possible only if steals can occur.
void cilk_spawn_or_continue(int in_continuation)
{
  cilkprof_stack_t *stack = &(GET_STACK(ctx_stack));

  assert(!(stack->in_user_code));
  if (in_continuation) {
    // In the continuation
    WHEN_TRACE_CALLS(
        fprintf(stderr, "cilk_spawn_or_continue(%d) from continuation [ret %p]\n", in_continuation,
                __builtin_extract_return_addr(__builtin_return_address(0))); );
    stack->in_user_code = true;

#if COMPUTE_STRAND_DATA
    stack->strand_start
      = (uintptr_t)__builtin_extract_return_addr(__builtin_return_address(0));
#endif
    begin_strand(stack);
  } else {
    // In the spawned child
    WHEN_TRACE_CALLS(
        fprintf(stderr, "cilk_spawn_or_continue(%d) from spawn [ret %p]\n", in_continuation,
                __builtin_extract_return_addr(__builtin_return_address(0))); );
    // We need to re-enter user code, because function calls for
    // arguments might be called before enter_helper_begin occurs in
    // spawn helper.
    stack->in_user_code = true;

#if COMPUTE_STRAND_DATA
    stack->strand_start
      = (uintptr_t)__builtin_extract_return_addr(__builtin_return_address(0));
#endif
    begin_strand(stack);
  }
}

void cilk_detach_begin(__cilkrts_stack_frame *parent)
{
  WHEN_TRACE_CALLS( fprintf(stderr, "cilk_detach_begin(%p) [ret %p]\n", parent,
                            __builtin_extract_return_addr(__builtin_return_address(0))); );

  cilkprof_stack_t *stack = &(GET_STACK(ctx_stack));
  assert(HELPER == stack->bot->func_type);

#if COMPUTE_STRAND_DATA
  // Prologue disabled
  stack->strand_end
      = (uintptr_t)__builtin_extract_return_addr(__builtin_return_address(0));
#endif
  measure_and_add_strand_length(stack);

  assert(stack->in_user_code);
  stack->in_user_code = false;

  return;
}

void cilk_detach_end(void)
{
  WHEN_TRACE_CALLS( fprintf(stderr, "cilk_detach_end() [ret %p]\n",
                            __builtin_extract_return_addr(__builtin_return_address(0))); );

  cilkprof_stack_t *stack = &(GET_STACK(ctx_stack));
  
  assert(!(stack->in_user_code));
  stack->in_user_code = true;

#if COMPUTE_STRAND_DATA
  // Prologue disabled
  stack->strand_start
      = (uintptr_t)__builtin_extract_return_addr(__builtin_return_address(0));
#endif
  begin_strand(stack);

  return;
}

void cilk_sync_begin(__cilkrts_stack_frame *sf)
{
  cilkprof_stack_t *stack = &(GET_STACK(ctx_stack));

#if COMPUTE_STRAND_DATA
  stack->strand_end
      = (uintptr_t)__builtin_extract_return_addr(__builtin_return_address(0));
#endif
  measure_and_add_strand_length(stack);

  if (SPAWNER == stack->bot->func_type) {
    WHEN_TRACE_CALLS( fprintf(stderr, "cilk_sync_begin(%p) from SPAWNER [ret %p]\n", sf,
                              __builtin_extract_return_addr(__builtin_return_address(0))); );
  } else {
    WHEN_TRACE_CALLS( fprintf(stderr, "cilk_sync_begin(%p) from HELPER [ret %p]\n", sf,
                              __builtin_extract_return_addr(__builtin_return_address(0))); );
  }

  assert(stack->in_user_code);
  stack->in_user_code = false;
}

void cilk_sync_end(__cilkrts_stack_frame *sf)
{
  cilkprof_stack_t *stack = &(GET_STACK(ctx_stack));

  if (stack->bot->lchild_spn > stack->bot->contin_spn) {
    stack->bot->prefix_spn += stack->bot->lchild_spn;
    // local_spn does not increase, because critical path goes through
    // spawned child.
    add_cc_hashtables(&(stack->bot->prefix_table), &(stack->bot->lchild_table));
#if COMPUTE_STRAND_DATA
    add_strand_hashtables(&(stack->bot->strand_prefix_table), &(stack->bot->strand_lchild_table));
#endif
  } else {
    stack->bot->prefix_spn += stack->bot->contin_spn;
    // critical path goes through continuation, which is local.  add
    // local_contin to local_spn.
    stack->bot->local_spn += stack->bot->local_contin;
    add_cc_hashtables(&(stack->bot->prefix_table), &(stack->bot->contin_table));
#if COMPUTE_STRAND_DATA
    add_strand_hashtables(&(stack->bot->strand_prefix_table), &(stack->bot->strand_contin_table));
#endif
  }

  // reset lchild and contin span variables
  stack->bot->lchild_spn = 0;
  stack->bot->contin_spn = 0;
  stack->bot->local_contin = 0;
  clear_cc_hashtable(stack->bot->lchild_table);
  clear_cc_hashtable(stack->bot->contin_table);
  clear_strand_hashtable(stack->bot->strand_lchild_table);
  clear_strand_hashtable(stack->bot->strand_contin_table);
  
  // can't be anything else; only SPAWNER have sync
  assert(SPAWNER == stack->bot->func_type); 
  assert(!(stack->in_user_code));
  stack->in_user_code = true;
  WHEN_TRACE_CALLS( fprintf(stderr, "cilk_sync_end(%p) from SPAWNER [ret %p]\n", sf,
                            __builtin_extract_return_addr(__builtin_return_address(0))); );
#if COMPUTE_STRAND_DATA
  stack->strand_start
      = (uintptr_t)__builtin_extract_return_addr(__builtin_return_address(0));
#endif
  begin_strand(stack);
}

void cilk_leave_begin(__cilkrts_stack_frame *sf)
{
  WHEN_TRACE_CALLS( fprintf(stderr, "cilk_leave_begin(%p) [ret %p]\n", sf,
                            __builtin_extract_return_addr(__builtin_return_address(0))); );

  cilkprof_stack_t *stack = &(GET_STACK(ctx_stack));

  cilkprof_stack_frame_t *old_bottom;
  bool add_success;

#if COMPUTE_STRAND_DATA
  // Epilogues disabled
  stack->strand_end
      = (uintptr_t)__builtin_extract_return_addr(__builtin_return_address(0));
#endif
  measure_and_add_strand_length(stack);

  assert(stack->in_user_code);
  stack->in_user_code = false;

  // We are leaving this function, so it must have sync-ed, meaning
  // that, lchild should be 0 / empty.  prefix could contain value,
  // however, if this function is a Cilk function that spawned before.
  assert(0 == stack->bot->lchild_spn);
  assert(cc_hashtable_is_empty(stack->bot->lchild_table));
#if COMPUTE_STRAND_DATA
  assert(strand_hashtable_is_empty(stack->bot->strand_lchild_table));
#endif

  stack->bot->prefix_spn += stack->bot->contin_spn;
  stack->bot->local_spn += stack->bot->local_contin;
  add_cc_hashtables(&(stack->bot->prefix_table), &(stack->bot->contin_table));
#if COMPUTE_STRAND_DATA
  add_strand_hashtables(&(stack->bot->strand_prefix_table), &(stack->bot->strand_contin_table));
#endif

  // Pop the stack
  old_bottom = cilkprof_stack_pop(stack);
  int32_t min_cs_depth = exit_call_site(&(stack->unique_call_sites),
                                        old_bottom->rip, old_bottom->function,
                                        old_bottom->depth);

  stack->bot->running_wrk += old_bottom->running_wrk;

  InstanceType_t inst_type
      = (RECURSIVE & -(INT32_MAX != min_cs_depth))
      | (TOP & -(!function_on_stack_above(stack->unique_call_sites,
                                          stack->bot->function,
                                          stack->bot->depth)));
  // Update work table
  if (INT32_MAX == min_cs_depth || min_cs_depth == old_bottom->depth) {
    /* fprintf(stderr, "adding to wrk table\n"); */
    add_success = add_to_cc_hashtable(&(stack->wrk_table),
                                      inst_type | RECORD,
                                      old_bottom->func_type,
                                      old_bottom->rip,
                                      old_bottom->running_wrk,
                                      old_bottom->prefix_spn,
                                      old_bottom->local_wrk,
                                      old_bottom->local_spn);
    assert(add_success);
    /* fprintf(stderr, "adding to prefix table\n"); */
    add_success = add_to_cc_hashtable(&(old_bottom->prefix_table),
                                      inst_type | RECORD,
                                      old_bottom->func_type,
                                      old_bottom->rip,
                                      old_bottom->running_wrk,
                                      old_bottom->prefix_spn,
                                      old_bottom->local_wrk,
                                      old_bottom->local_spn);
    assert(add_success);
  } else {
    // Only record the local work and local span
    /* fprintf(stderr, "adding to wrk table\n"); */
    add_success = add_to_cc_hashtable(&(stack->wrk_table),
                                      0,
                                      old_bottom->func_type,
                                      old_bottom->rip,
                                      0,
                                      0,
                                      old_bottom->local_wrk,
                                      old_bottom->local_spn);
    assert(add_success);
    /* fprintf(stderr, "adding to prefix table\n"); */
    add_success = add_to_cc_hashtable(&(old_bottom->prefix_table),
                                      0,
                                      old_bottom->func_type,
                                      old_bottom->rip,
                                      0,
                                      0,
                                      old_bottom->local_wrk,
                                      old_bottom->local_spn);
    assert(add_success);
  }

  /* bool is_recursive = exit_call_site(&(stack->unique_call_sites), */
  /*                                    old_bottom->rip, old_bottom->function, */
  /*                                    old_bottom->depth); */
  /* // If the call site is not recursive -- it did not appear multiple */
  /* // times on the stack -- then use INT32_MAX as the depth. */
  /* int32_t depth = is_recursive ? old_bottom->depth : INT32_MAX; */
  /* if (!is_recursive || */
  /*     !function_on_stack_above(stack->unique_call_sites, */
  /*                              stack->bot->function, stack->bot->depth)) { */
  /*   /\* fprintf(stderr, "adding to wrk table\n"); *\/ */
  /*   add_success = add_to_cc_hashtable(&(stack->wrk_table), */
  /*                                     depth, */
  /*                                     old_bottom->func_type, */
  /*                                     old_bottom->rip, */
  /*                                     old_bottom->running_wrk, */
  /*                                     old_bottom->prefix_spn, */
  /*                                     old_bottom->local_wrk, */
  /*                                     old_bottom->local_spn); */
  /*   assert(add_success); */
  /*   /\* fprintf(stderr, "adding to prefix table\n"); *\/ */
  /*   add_success = add_to_cc_hashtable(&(old_bottom->prefix_table), */
  /*                                     depth, */
  /*                                     old_bottom->func_type, */
  /*                                     old_bottom->rip, */
  /*                                     old_bottom->running_wrk, */
  /*                                     old_bottom->prefix_spn, */
  /*                                     old_bottom->local_wrk, */
  /*                                     old_bottom->local_spn); */
  /*   assert(add_success); */
  /* } else { */
  /*   /\* fprintf(stderr, "adding to wrk table\n"); *\/ */
  /*   add_success = add_to_cc_hashtable(&(stack->wrk_table), */
  /*                                     INT32_MAX, */
  /*                                     old_bottom->func_type, */
  /*                                     old_bottom->rip, */
  /*                                     0, */
  /*                                     0, */
  /*                                     old_bottom->local_wrk, */
  /*                                     old_bottom->local_spn); */
  /*   assert(add_success); */
  /*   /\* fprintf(stderr, "adding to prefix table\n"); *\/ */
  /*   add_success = add_to_cc_hashtable(&(old_bottom->prefix_table), */
  /*                                     INT32_MAX, */
  /*                                     old_bottom->func_type, */
  /*                                     old_bottom->rip, */
  /*                                     0, */
  /*                                     0, */
  /*                                     old_bottom->local_wrk, */
  /*                                     old_bottom->local_spn); */
  /*   assert(add_success); */
  /* } */

  if (SPAWNER == old_bottom->func_type) {
    // This is the case we are returning to a call, since a SPAWNER
    // is always called by a spawn helper.

    assert(NULL != old_bottom->parent);

    // Update continuation variable
    stack->bot->contin_spn += old_bottom->prefix_spn;
    // Don't increment local_spn for new stack->bot.
    /* fprintf(stderr, "adding tables\n"); */
    add_cc_hashtables(&(stack->bot->contin_table), &(old_bottom->prefix_table));
#if COMPUTE_STRAND_DATA
    add_strand_hashtables(&(stack->bot->strand_contin_table), &(old_bottom->strand_prefix_table));
#endif

    free(old_bottom->prefix_table);
    free(old_bottom->lchild_table);
    free(old_bottom->contin_table);
    free(old_bottom->strand_prefix_table);
    free(old_bottom->strand_lchild_table);
    free(old_bottom->strand_contin_table);

  } else {
    // This is the case we are returning to a spawn, since a HELPER 
    // is always invoked due to a spawn statement.

    assert(HELPER != stack->bot->func_type);

    if (stack->bot->contin_spn + old_bottom->prefix_spn > stack->bot->lchild_spn) {
      // fprintf(stderr, "updating longest child\n");
      stack->bot->prefix_spn += stack->bot->contin_spn;
      stack->bot->local_spn += stack->bot->local_contin;
      // This needs a better data structure to be implemented more
      // efficiently.
      add_cc_hashtables(&(stack->bot->prefix_table), &(stack->bot->contin_table));
#if COMPUTE_STRAND_DATA
      add_strand_hashtables(&(stack->bot->strand_prefix_table), &(stack->bot->strand_contin_table));
#endif

      // Save old_bottom tables in new bottom's l_child variable.
      stack->bot->lchild_spn = old_bottom->prefix_spn;
      free(stack->bot->lchild_table);
      free(stack->bot->strand_lchild_table);
      stack->bot->lchild_table = old_bottom->prefix_table;
      stack->bot->strand_lchild_table = old_bottom->strand_prefix_table;

      // Free old_bottom tables that are no longer in use
      free(old_bottom->lchild_table);
      free(old_bottom->contin_table);
      free(old_bottom->strand_lchild_table);
      free(old_bottom->strand_contin_table);

      // Empy new bottom's continuation
      stack->bot->contin_spn = 0;
      stack->bot->local_contin = 0;
      clear_cc_hashtable(stack->bot->contin_table);
      clear_strand_hashtable(stack->bot->strand_contin_table);

    } else {
      // Discared all tables from old_bottom
      free(old_bottom->prefix_table);
      free(old_bottom->lchild_table);
      free(old_bottom->contin_table);
      free(old_bottom->strand_prefix_table);
      free(old_bottom->strand_lchild_table);
      free(old_bottom->strand_contin_table);
    }
  }

  free(old_bottom);
}

void cilk_leave_end(void)
{
  cilkprof_stack_t *stack = &(GET_STACK(ctx_stack));

#if TRACE_CALLS
  switch(stack->bot->func_type) {
    case HELPER:
      fprintf(stderr, "cilk_leave_end() from HELPER [ret %p]\n",
              __builtin_extract_return_addr(__builtin_return_address(0)));
      break;
    case SPAWNER:
      fprintf(stderr, "cilk_leave_end() from SPAWNER [ret %p]\n",
              __builtin_extract_return_addr(__builtin_return_address(0)));
      break;
    case MAIN:
      fprintf(stderr, "cilk_leave_end() from MAIN [ret %p]\n",
              __builtin_extract_return_addr(__builtin_return_address(0)));
      break;
    case C_FUNCTION:
      // We can have leave_end from C_FUNCTION because leave_begin
      // popped the stack already
      fprintf(stderr, "cilk_leave_end() from C_FUNCTION [ret %p]\n",
              __builtin_extract_return_addr(__builtin_return_address(0)));
      break;
    default:
      assert(false && "Should not reach this point.");
  }
#endif

  assert(!(stack->in_user_code));
  stack->in_user_code = true;
#if COMPUTE_STRAND_DATA
  // Epilogues disabled
  stack->strand_start
      = (uintptr_t)__builtin_extract_return_addr(__builtin_return_address(0));
#endif
  begin_strand(stack);
}

