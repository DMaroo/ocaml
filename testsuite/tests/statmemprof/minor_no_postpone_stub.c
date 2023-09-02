#include "caml/alloc.h"

value alloc_stub(value v) {
  return my_alloc(1);
}
