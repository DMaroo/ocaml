#pragma once

#include <stddef.h>

struct HeapRange {
  size_t first_header;
  size_t rightmost_value;
};

extern struct HeapRange get_heap_range();
