#include "gc.h"
#include "heap.h"
#include <stddef.h>
#include <stdint.h>

#define CAML_INTERNALS
#include "../caml/misc.h"
#include "../caml/mlvalues.h"

// runtime defines alloc to be caml_alloc, we don't want that here
#undef alloc

extern uint8_t *alloc(unsigned long long);

void verified_gc() {
  mark_and_sweep(get_heap_range().first_header,
                 get_heap_range().rightmost_value);
}

void *verified_allocate(unsigned long long wsize) {
  // printf("Allocation request for %lld\n", wsize);
  uint8_t *mem = alloc(wsize);
  int oom_count = 0;

again:
  if (((uintptr_t)mem - sizeof(uintptr_t)) == 0) {
    oom_count++;
    if (oom_count == 2) {
      // Exit
      caml_fatal_error("Allocator OOM");
    }

    verified_gc();

    mem = alloc(wsize);
    goto again;
  }
  return mem - 8U;
}

value verified_trigger_gc(value unit) {
  verified_gc();
  return Val_unit;
}
