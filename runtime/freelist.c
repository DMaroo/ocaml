/**************************************************************************/
/*                                                                        */
/*                                 OCaml                                  */
/*                                                                        */
/*              Damien Doligez, projet Para, INRIA Rocquencourt           */
/*                                                                        */
/*   Copyright 1996 Institut National de Recherche en Informatique et     */
/*     en Automatique.                                                    */
/*                                                                        */
/*   All rights reserved.  This file is distributed under the terms of    */
/*   the GNU Lesser General Public License version 2.1, with the          */
/*   special exception on linking described in the file LICENSE.          */
/*                                                                        */
/**************************************************************************/

#define CAML_INTERNALS

#define FREELIST_DEBUG 0
#if FREELIST_DEBUG
#include <stdio.h>
#endif

#include <string.h>

#include "caml/config.h"
#include "caml/custom.h"
#include "caml/freelist.h"
#include "caml/gc.h"
#include "caml/gc_ctrl.h"
#include "caml/memory.h"
#include "caml/major_gc.h"
#include "caml/misc.h"
#include "caml/mlvalues.h"
#include "caml/eventlog.h"

/*************** declarations common to all policies ******************/

/* A block in a small free list is a [value] (integer representing a
   pointer to the first word after the block's header). The end of the
  list is NULL.
*/
#define Val_NULL ((value) NULL)

asize_t caml_fl_cur_wsz = 0;     /* Number of words in the free set,
                                    including headers but not fragments. */

value caml_fl_merge = Val_NULL;  /* Current insertion pointer.  Managed
                                    jointly with [sweep_slice]. */

/* Next in list */
#define Next_small(v) Field ((v), 0)

/* Next in memory order */
Caml_inline value Next_in_mem (value v) {
  return (value) &Field ((v), Whsize_val (v));
}

#ifdef CAML_INSTR

/* number of pointers followed to allocate from the free set */
uintnat caml_instr_alloc_jump = 0;

#define EV_ALLOC_JUMP(n) (caml_instr_alloc_jump += (n))

#endif /*CAML_INSTR*/



/********************* next-fit allocation policy *********************/

/* The free-list is kept sorted by increasing addresses.
   This makes the merging of adjacent free blocks possible.
   (See [nf_merge_block].)
*/

/* The sentinel can be located anywhere in memory, but it must not be
   adjacent to any heap object. */
static struct {
  value filler1; /* Make sure the sentinel is never adjacent to any block. */
  header_t h;
  value first_field;
  value filler2; /* Make sure the sentinel is never adjacent to any block. */
} nf_sentinel = {0, Make_header (0, 0, Caml_blue), Val_NULL, 0};

#define Nf_head (Val_bp (&(nf_sentinel.first_field)))

static value nf_prev = Nf_head;  /* Current allocation pointer. */

#if defined (DEBUG) || FREELIST_DEBUG
static void nf_check (void)
{
  value cur;
  int prev_found = 0, merge_found = 0;
  uintnat size_found = 0;

  cur = Next_small (Nf_head);
  while (cur != Val_NULL){
    size_found += Whsize_bp (cur);
    CAMLassert (Is_in_heap (cur));
    if (cur == nf_prev) prev_found = 1;
    if (cur == caml_fl_merge) merge_found = 1;
    cur = Next_small (cur);
  }
  CAMLassert (prev_found || nf_prev == Nf_head);
  CAMLassert (merge_found || caml_fl_merge == Nf_head);
  CAMLassert (size_found == caml_fl_cur_wsz);
}

#endif /* DEBUG || FREELIST_DEBUG */

/* Location of the last fragment seen by the sweeping code.
   This is a pointer to the first word after the fragment, which is
   the header of the next block.
   Note that [last_fragment] doesn't point to the fragment itself,
   but to the block after it.
*/
static header_t *nf_last_fragment;

static void nf_init_merge (void)
{
  CAML_EV_ALLOC_FLUSH();
  nf_last_fragment = NULL;
  caml_fl_merge = Nf_head;
#ifdef DEBUG
  nf_check ();
#endif
}

static void nf_init (void)
{
  Next_small (Nf_head) = Val_NULL;
  nf_prev = Nf_head;
  caml_fl_cur_wsz = 0;
}

static void nf_reset (void)
{
  nf_init ();
}

/* Note: the [limit] parameter is unused because we merge blocks one by one. */
static header_t *nf_merge_block (value bp, char *limit)
{
  value prev, cur, adj;
  header_t hd = Hd_val (bp);
  mlsize_t prev_wosz;

  caml_fl_cur_wsz += Whsize_hd (hd);

  /* [merge_block] is now responsible for calling the finalization function. */
  if (Tag_hd (hd) == Custom_tag){
    void (*final_fun)(value) = Custom_ops_val(bp)->finalize;
    if (final_fun != NULL) final_fun(bp);
  }

#ifdef DEBUG
  caml_set_fields (bp, 0, Debug_free_major);
#endif
  prev = caml_fl_merge;
  cur = Next_small (prev);
  /* The sweep code makes sure that this is the right place to insert
     this block: */
  CAMLassert (Bp_val (prev) < Bp_val (bp) || prev == Nf_head);
  CAMLassert (Bp_val (cur) > Bp_val (bp) || cur == Val_NULL);

  /* If [last_fragment] and [bp] are adjacent, merge them. */
  if (nf_last_fragment == Hp_val (bp)){
    mlsize_t bp_whsz = Whsize_val (bp);
    if (bp_whsz <= Max_wosize){
      hd = Make_header (bp_whsz, 0, Caml_white);
      bp = (value) nf_last_fragment;
      Hd_val (bp) = hd;
      caml_fl_cur_wsz += Whsize_wosize (0);
    }
  }

  /* If [bp] and [cur] are adjacent, remove [cur] from the free-list
     and merge them. */
  adj = Next_in_mem (bp);
  if (adj == cur){
    value next_cur = Next_small (cur);
    mlsize_t cur_whsz = Whsize_val (cur);

    if (Wosize_hd (hd) + cur_whsz <= Max_wosize){
      Next_small (prev) = next_cur;
      if (nf_prev == cur) nf_prev = prev;
      hd = Make_header (Wosize_hd (hd) + cur_whsz, 0, Caml_blue);
      Hd_val (bp) = hd;
      adj = Next_in_mem (bp);
#ifdef DEBUG
      Next_small (cur) = (value) Debug_free_major;
      Hd_val (cur) = Debug_free_major;
#endif
      cur = next_cur;
    }
  }
  /* If [prev] and [bp] are adjacent merge them, else insert [bp] into
     the free-list if it is big enough. */
  prev_wosz = Wosize_val (prev);
  if (Next_in_mem (prev) == bp && prev_wosz + Whsize_hd (hd) < Max_wosize){
    Hd_val (prev) = Make_header (prev_wosz + Whsize_hd (hd), 0, Caml_blue);
#ifdef DEBUG
    Hd_val (bp) = Debug_free_major;
#endif
    CAMLassert (caml_fl_merge == prev);
  }else if (Wosize_hd (hd) != 0){
    Hd_val (bp) = Bluehd_hd (hd);
    Next_small (bp) = cur;
    Next_small (prev) = bp;
    caml_fl_merge = bp;
  }else{
    /* This is a fragment.  Leave it in white but remember it for eventual
       merging with the next block. */
    nf_last_fragment = (header_t *) bp;
    caml_fl_cur_wsz -= Whsize_wosize (0);
  }
  return Hp_val (adj);
}

static void nf_make_free_blocks
  (value *p, mlsize_t size, int do_merge, int color)
{
  mlsize_t sz;

  while (size > 0){
    if (size > Whsize_wosize (Max_wosize)){
      sz = Whsize_wosize (Max_wosize);
    }else{
      sz = size;
    }
    *(header_t *)p = Make_header (Wosize_whsize (sz), 0, color);
    if (do_merge) nf_merge_block (Val_hp (p), NULL);
    size -= sz;
    p += sz;
  }
}

/******************** first-fit allocation policy *********************/

#define FLP_MAX 1000
static value flp [FLP_MAX];
static int flp_size = 0;
static value beyond = Val_NULL;

/* The sentinel can be located anywhere in memory, but it must not be
   adjacent to any heap object. */
static struct {
  value filler1; /* Make sure the sentinel is never adjacent to any block. */
  header_t h;
  value first_field;
  value filler2; /* Make sure the sentinel is never adjacent to any block. */
} ff_sentinel = {0, Make_header (0, 0, Caml_blue), Val_NULL, 0};

#define Ff_head (Val_bp (&(ff_sentinel.first_field)))


#if defined (DEBUG) || FREELIST_DEBUG
static void ff_check (void)
{
  value cur;
  int flp_found = 0, merge_found = 0;
  uintnat size_found = 0;
  int sz = 0;

  cur = Next_small (Ff_head);
  while (cur != Val_NULL){
    size_found += Whsize_bp (cur);
    CAMLassert (Is_in_heap (cur));
    if (Wosize_bp (cur) > sz){
      sz = Wosize_bp (cur);
      if (flp_found < flp_size){
        CAMLassert (Next_small (flp[flp_found]) == cur);
        ++ flp_found;
      }else{
        CAMLassert (beyond == Val_NULL
                    || Bp_val (cur) >= Bp_val (Next_small (beyond)));
      }
    }
    if (cur == caml_fl_merge) merge_found = 1;
    cur = Next_small (cur);
  }
  CAMLassert (flp_found == flp_size);
  CAMLassert (merge_found || caml_fl_merge == Ff_head);
  CAMLassert (size_found == caml_fl_cur_wsz);
}
#endif /* DEBUG || FREELIST_DEBUG */

/* Location of the last fragment seen by the sweeping code.
   This is a pointer to the first word after the fragment, which is
   the header of the next block.
   Note that [ff_last_fragment] doesn't point to the fragment itself,
   but to the block after it.
*/
static header_t *ff_last_fragment;

static void ff_init_merge (void)
{
  CAML_EV_ALLOC_FLUSH();
  ff_last_fragment = NULL;
  caml_fl_merge = Ff_head;
#ifdef DEBUG
  ff_check ();
#endif
}

static void ff_truncate_flp (value changed)
{
  if (changed == Ff_head){
    flp_size = 0;
    beyond = Val_NULL;
  }else{
    while (flp_size > 0 &&
           Bp_val (Next_small (flp[flp_size - 1])) >= Bp_val (changed))
      -- flp_size;
    if (Bp_val (beyond) >= Bp_val (changed)) beyond = Val_NULL;
  }
}

static void ff_init (void)
{
  Next_small (Ff_head) = Val_NULL;
  ff_truncate_flp (Ff_head);
  caml_fl_cur_wsz = 0;
}

static void ff_reset (void)
{
  ff_init ();
}

/* Note: the [limit] parameter is unused because we merge blocks one by one. */
static header_t *ff_merge_block (value bp, char *limit)
{
  value prev, cur, adj;
  header_t hd = Hd_val (bp);
  mlsize_t prev_wosz;

  caml_fl_cur_wsz += Whsize_hd (hd);

  /* [merge_block] is now responsible for calling the finalization function. */
  if (Tag_hd (hd) == Custom_tag){
    void (*final_fun)(value) = Custom_ops_val(bp)->finalize;
    if (final_fun != NULL) final_fun(bp);
  }

#ifdef DEBUG
  caml_set_fields (bp, 0, Debug_free_major);
#endif
  prev = caml_fl_merge;
  cur = Next_small (prev);
  /* The sweep code makes sure that this is the right place to insert
     this block: */
  CAMLassert (Bp_val (prev) < Bp_val (bp) || prev == Ff_head);
  CAMLassert (Bp_val (cur) > Bp_val (bp) || cur == Val_NULL);

  ff_truncate_flp (prev);

  /* If [ff_last_fragment] and [bp] are adjacent, merge them. */
  if (ff_last_fragment == Hp_bp (bp)){
    mlsize_t bp_whsz = Whsize_val (bp);
    if (bp_whsz <= Max_wosize){
      hd = Make_header (bp_whsz, 0, Caml_white);
      bp = (value) ff_last_fragment;
      Hd_val (bp) = hd;
      caml_fl_cur_wsz += Whsize_wosize (0);
    }
  }

  /* If [bp] and [cur] are adjacent, remove [cur] from the free-list
     and merge them. */
  adj = Next_in_mem (bp);
  if (adj == cur){
    value next_cur = Next_small (cur);
    mlsize_t cur_whsz = Whsize_val (cur);

    if (Wosize_hd (hd) + cur_whsz <= Max_wosize){
      Next_small (prev) = next_cur;
      hd = Make_header (Wosize_hd (hd) + cur_whsz, 0, Caml_blue);
      Hd_val (bp) = hd;
      adj = Next_in_mem (bp);
#ifdef DEBUG
      Next_small (cur) = (value) Debug_free_major;
      Hd_val (cur) = Debug_free_major;
#endif
      cur = next_cur;
    }
  }
  /* If [prev] and [bp] are adjacent merge them, else insert [bp] into
     the free-list if it is big enough. */
  prev_wosz = Wosize_val (prev);
  if (Next_in_mem (prev) == bp && prev_wosz + Whsize_hd (hd) < Max_wosize){
    Hd_val (prev) = Make_header (prev_wosz + Whsize_hd (hd), 0, Caml_blue);
#ifdef DEBUG
    Hd_val (bp) = Debug_free_major;
#endif
    CAMLassert (caml_fl_merge == prev);
  }else if (Wosize_hd (hd) != 0){
    Hd_val (bp) = Bluehd_hd (hd);
    Next_small (bp) = cur;
    Next_small (prev) = bp;
    caml_fl_merge = bp;
  }else{
    /* This is a fragment.  Leave it in white but remember it for eventual
       merging with the next block. */
    ff_last_fragment = (header_t *) bp;
    caml_fl_cur_wsz -= Whsize_wosize (0);
  }
  return Hp_val (adj);
}

static void ff_make_free_blocks
  (value *p, mlsize_t size, int do_merge, int color)
{
  mlsize_t sz;

  while (size > 0){
    if (size > Whsize_wosize (Max_wosize)){
      sz = Whsize_wosize (Max_wosize);
    }else{
      sz = size;
    }
    *(header_t *)p = Make_header (Wosize_whsize (sz), 0, color);
    if (do_merge) ff_merge_block (Val_hp (p), NULL);
    size -= sz;
    p += sz;
  }
}

/********************* best-fit allocation policy *********************/

/* quick-fit + FIFO-ordered best fit (Wilson's nomenclature)
   We use Standish's data structure (a tree of doubly-linked lists)
   with a splay tree (Sleator & Tarjan).
*/

/* [BF_NUM_SMALL] must be at least 4 for this code to work
   and at least 5 for good performance on typical OCaml programs.
   For portability reasons, BF_NUM_SMALL cannot be more than 32.
*/
#define BF_NUM_SMALL 16

/* Note that indexing into [bf_small_fl] starts at 1, so the first entry
   in this array is unused.
*/
static struct {
  value free;
  value *merge;
} bf_small_fl [BF_NUM_SMALL + 1];
static int bf_small_map = 0;

/* Small free blocks have only one pointer to the next block.
   Large free blocks have 5 fields:
   tree fields:
     - isnode flag
     - left child
     - right child
   list fields:
     - next
     - prev
*/
typedef struct large_free_block {
  int isnode;
  struct large_free_block *left;
  struct large_free_block *right;
  struct large_free_block *prev;
  struct large_free_block *next;
} large_free_block;

Caml_inline mlsize_t bf_large_wosize (struct large_free_block *n) {
  return Wosize_val((value)(n));
}

static struct large_free_block *bf_large_tree;
static struct large_free_block *bf_large_least;
/* [bf_large_least] is either NULL or a pointer to the smallest (leftmost)
   block in the tree. In this latter case, the block must be alone in its
   doubly-linked list (i.e. have [isnode] true and [prev] and [next]
   both pointing back to this block)
*/

/* Auxiliary functions for bitmap */

/* Find first (i.e. least significant) bit set in a word. */
#ifdef HAS_FFS
#include <strings.h>
#elif defined(HAS_BITSCANFORWARD)
#include <intrin.h>
Caml_inline int ffs (int x)
{
  unsigned long index;
  unsigned char result;
  result = _BitScanForward (&index, (unsigned long) x);
  return result ? (int) index + 1 : 0;
}
#else
Caml_inline int ffs (int x)
{
  /* adapted from Hacker's Delight */
  int bnz, b0, b1, b2, b3, b4;
  CAMLassert ((x & 0xFFFFFFFF) == x);
  x = x & -x;
  bnz = x != 0;
  b4 = !!(x & 0xFFFF0000) << 4;
  b3 = !!(x & 0xFF00FF00) << 3;
  b2 = !!(x & 0xF0F0F0F0) << 2;
  b1 = !!(x & 0xCCCCCCCC) << 1;
  b0 = !!(x & 0xAAAAAAAA);
  return bnz + b0 + b1 + b2 + b3 + b4;
}
#endif /* HAS_FFS or HAS_BITSCANFORWARD */

/* Indexing starts at 1 because that's the minimum block size. */
Caml_inline void set_map (int index)
{
  bf_small_map |= (1 << (index - 1));
}
Caml_inline void unset_map (int index)
{
  bf_small_map &= ~(1 << (index - 1));
}


/* debug functions for checking the data structures */

#if defined (DEBUG) || FREELIST_DEBUG

static mlsize_t bf_check_cur_size = 0;
static asize_t bf_check_subtree (large_free_block *p)
{
  mlsize_t wosz;
  large_free_block *cur, *next;
  asize_t total_size = 0;

  if (p == NULL) return 0;

  wosz = bf_large_wosize(p);
  CAMLassert (p->isnode == 1);
  total_size += bf_check_subtree (p->left);
  CAMLassert (wosz > BF_NUM_SMALL);
  CAMLassert (wosz > bf_check_cur_size);
  bf_check_cur_size = wosz;
  cur = p;
  while (1){
    CAMLassert (bf_large_wosize (cur) == wosz);
    CAMLassert (Color_val ((value) cur) == Caml_blue);
    CAMLassert ((cur == p && cur->isnode == 1) || cur->isnode == 0);
    total_size += Whsize_wosize (wosz);
    next = cur->next;
    CAMLassert (next->prev == cur);
    if (next == p) break;
    cur = next;
  }
  total_size += bf_check_subtree (p->right);
  return total_size;
}

static void bf_check (void)
{
  mlsize_t i;
  asize_t total_size = 0;
  int map = 0;

  /* check free lists */
  CAMLassert (BF_NUM_SMALL <= 8 * sizeof (int));
  for (i = 1; i <= BF_NUM_SMALL; i++){
    value b;
    int col = 0;
    int merge_found = 0;

    if (bf_small_fl[i].merge == &bf_small_fl[i].free){
      merge_found = 1;
    }else{
      CAMLassert (caml_gc_phase != Phase_sweep
                  || caml_fl_merge == Val_NULL
                  || bf_small_fl[i].merge < &Next_small(caml_fl_merge));
    }
    CAMLassert (*bf_small_fl[i].merge == Val_NULL
                || Color_val (*bf_small_fl[i].merge) == Caml_blue);
    if (bf_small_fl[i].free != Val_NULL) map |= 1 << (i-1);
    for (b = bf_small_fl[i].free; b != Val_NULL; b = Next_small (b)){
      if (bf_small_fl[i].merge == &Next_small (b)) merge_found = 1;
      CAMLassert (Wosize_val (b) == i);
      total_size += Whsize_wosize (i);
      if (Color_val (b) == Caml_blue){
        col = 1;
        CAMLassert (Next_small (b) == Val_NULL
                    || Bp_val (Next_small (b)) > Bp_val (b));
      }else{
        CAMLassert (col == 0);
        CAMLassert (Color_val (b) == Caml_white);
      }
    }
    if (caml_gc_phase == Phase_sweep) CAMLassert (merge_found);
  }
  CAMLassert (map == bf_small_map);
  /* check [caml_fl_merge] */
  CAMLassert (caml_gc_phase != Phase_sweep
              || caml_fl_merge == Val_NULL
              || Hp_val (caml_fl_merge) < (header_t *) caml_gc_sweep_hp);
  /* check the tree */
  bf_check_cur_size = 0;
  total_size += bf_check_subtree (bf_large_tree);
  /* check the total free set size */
  CAMLassert (total_size == caml_fl_cur_wsz);
  /* check the smallest-block pointer */
  if (bf_large_least != NULL){
    large_free_block *x = bf_large_tree;
    while (x->left != NULL) x = x->left;
    CAMLassert (x == bf_large_least);
    CAMLassert (x->isnode == 1);
    CAMLassert (x->prev == x);
    CAMLassert (x->next == x);
  }
}

#endif /* DEBUG || FREELIST_DEBUG */

#if FREELIST_DEBUG
#define FREELIST_DEBUG_bf_check() bf_check ()
#else
#define FREELIST_DEBUG_bf_check()
#endif

/**************************************************************************/
/* splay trees */

/* Our tree is composed of nodes. Each node is the head of a doubly-linked
   circular list of blocks, all of the same size.
*/

/* Search for the node of the given size. Return a pointer to the pointer
   to the node, or a pointer to the NULL where the node should have been
   (it can be inserted here).
*/
static large_free_block **bf_search (mlsize_t wosz)
{
  large_free_block **p = &bf_large_tree;
  large_free_block *cur;
  mlsize_t cursz;

  while (1){
    cur = *p;
    CAML_EVENTLOG_DO(EV_ALLOC_JUMP (1));
    if (cur == NULL) break;
    cursz = bf_large_wosize (cur);
    if (cursz == wosz){
      break;
    }else if (cursz > wosz){
      p = &(cur->left);
    }else{
      CAMLassert (cursz < wosz);
      p = &(cur->right);
    }
  }
  return p;
}

/* Splay the tree at the given size. If a node of this size exists, it will
   become the root. If not, the last visited node will be the root. This is
   either the least node larger or the greatest node smaller than the given
   size.
   We use simple top-down splaying as described in S&T 85.
*/
static void bf_splay (mlsize_t wosz)
{
  large_free_block *x, *y;
  mlsize_t xsz;
  large_free_block *left_top = NULL;
  large_free_block *right_top = NULL;
  large_free_block **left_bottom = &left_top;
  large_free_block **right_bottom = &right_top;

  x = bf_large_tree;
  if (x == NULL) return;
  while (1){
    xsz = bf_large_wosize (x);
    if (xsz == wosz) break;
    if (xsz > wosz){
      /* zig */
      y = x->left;
      CAML_EVENTLOG_DO(EV_ALLOC_JUMP (1));
      if (y == NULL) break;
      if (bf_large_wosize (y) > wosz){
        /* zig-zig: rotate right */
        x->left = y->right;
        y->right = x;
        x = y;
        y = x->left;
        CAML_EVENTLOG_DO(EV_ALLOC_JUMP (2));
        if (y == NULL) break;
      }
      /* link right */
      *right_bottom = x;
      right_bottom = &(x->left);
      x = y;
    }else{
      CAMLassert (xsz < wosz);
      /* zag */
      y = x->right;
      CAML_EVENTLOG_DO(EV_ALLOC_JUMP (1));
      if (y == NULL) break;
      if (bf_large_wosize (y) < wosz){
        /* zag-zag : rotate left */
        x->right = y->left;
        y->left = x;
        x = y;
        y = x->right;
        CAML_EVENTLOG_DO(EV_ALLOC_JUMP (2));
        if (y == NULL) break;
      }
      /* link left */
      *left_bottom = x;
      left_bottom = &(x->right);
      x = y;
    }
  }
  /* reassemble the tree */
  *left_bottom = x->left;
  *right_bottom = x->right;
  x->left = left_top;
  x->right = right_top;
  CAML_EVENTLOG_DO(EV_ALLOC_JUMP (2));
  bf_large_tree = x;
}

/* Splay the subtree at [p] on its leftmost (least) node. After this
   operation, the root node of the subtree is the least node and it
   has no left child.
   The subtree must not be empty.
*/
static void bf_splay_least (large_free_block **p)
{
  large_free_block *x, *y;
  large_free_block *right_top = NULL;
  large_free_block **right_bottom = &right_top;

  x = *p;
  CAML_EVENTLOG_DO(EV_ALLOC_JUMP (1));
  CAMLassert (x != NULL);
  while (1){
    /* We are always in the zig case. */
    y = x->left;
    CAML_EVENTLOG_DO(EV_ALLOC_JUMP (1));
    if (y == NULL) break;
    /* And in the zig-zig case. rotate right */
    x->left = y->right;
    y->right = x;
    x = y;
    y = x->left;
    CAML_EVENTLOG_DO(EV_ALLOC_JUMP (2));
    if (y == NULL) break;
    /* link right */
    *right_bottom = x;
    right_bottom = &(x->left);
    x = y;
  }
  /* reassemble the tree */
  CAMLassert (x->left == NULL);
  *right_bottom = x->right;
  CAML_EVENTLOG_DO(EV_ALLOC_JUMP (1));
  x->right = right_top;
  *p = x;
}

/* Remove the node at [p], if any. */
static void bf_remove_node (large_free_block **p)
{
  large_free_block *x;
  large_free_block *l, *r;

  x = *p;
  CAML_EVENTLOG_DO(EV_ALLOC_JUMP (1));
  if (x == NULL) return;
  if (x == bf_large_least) bf_large_least = NULL;
  l = x->left;
  r = x->right;
  CAML_EVENTLOG_DO(EV_ALLOC_JUMP (2));
  if (l == NULL){
    *p = r;
  }else if (r == NULL){
    *p = l;
  }else{
    bf_splay_least (&r);
    r->left = l;
    *p = r;
  }
}

/* Insert a block into the tree, either as a new node or as a block in an
   existing list.
   Splay if the list is already present.
*/
static void bf_insert_block (large_free_block *n)
{
  mlsize_t sz = bf_large_wosize (n);
  large_free_block **p = bf_search (sz);
  large_free_block *x = *p;
  CAML_EVENTLOG_DO(EV_ALLOC_JUMP (1));

  if (bf_large_least != NULL){
    mlsize_t least_sz = bf_large_wosize (bf_large_least);
    if (sz < least_sz){
      CAMLassert (x == NULL);
      bf_large_least = n;
    }else if (sz == least_sz){
      CAMLassert (x == bf_large_least);
      bf_large_least = NULL;
    }
  }

  CAMLassert (Color_val ((value) n) == Caml_blue);
  CAMLassert (Wosize_val ((value) n) > BF_NUM_SMALL);
  if (x == NULL){
    /* add new node */
    n->isnode = 1;
    n->left = n->right = NULL;
    n->prev = n->next = n;
    *p = n;
  }else{
    /* insert at tail of doubly-linked list */
    CAMLassert (x->isnode == 1);
    n->isnode = 0;
#ifdef DEBUG
    n->left = n->right = (large_free_block *) Debug_free_unused;
#endif
    n->prev = x->prev;
    n->next = x;
    x->prev->next = n;
    x->prev = n;
    CAML_EVENTLOG_DO(EV_ALLOC_JUMP (2));
    bf_splay (sz);
  }
}

#if defined (DEBUG) || FREELIST_DEBUG
static int bf_is_in_tree (large_free_block *b)
{
  int wosz = bf_large_wosize (b);
  large_free_block **p = bf_search (wosz);
  large_free_block *n = *p;
  large_free_block *cur = n;

  if (n == NULL) return 0;
  while (1){
    if (cur == b) return 1;
    cur = cur->next;
    if (cur == n) return 0;
  }
}
#endif /* DEBUG || FREELIST_DEBUG */

/**************************************************************************/

/* Add back a remnant into a small free list. The block must be small
   and white (or a 0-size fragment).
   The block may be left out of the list depending on the sweeper's state.
   The free list size is updated accordingly.

   The block will be left out of the list if the GC is in its Sweep phase
   and the block is in the still-to-be-swept region because every block of
   the free list encountered by the sweeper must be blue and linked in
   its proper place in the increasing-addresses order of the list. This is
   to ensure that coalescing is always done when two or more free blocks
   are adjacent.
*/
static void bf_insert_remnant_small (value v)
{
  mlsize_t wosz = Wosize_val (v);

  CAMLassert (Color_val (v) == Caml_white);
  CAMLassert (wosz <= BF_NUM_SMALL);
  if (wosz != 0
      && (caml_gc_phase != Phase_sweep
          || (char *) Hp_val (v) < (char *) caml_gc_sweep_hp)){
    caml_fl_cur_wsz += Whsize_wosize (wosz);
    Next_small (v) = bf_small_fl[wosz].free;
    bf_small_fl[wosz].free = v;
    if (bf_small_fl[wosz].merge == &bf_small_fl[wosz].free){
      bf_small_fl[wosz].merge = &Next_small (v);
    }
    set_map (wosz);
  }
}

/* Add back a remnant into the free set. The block must have the
   appropriate color:
   - White if it is a fragment or a small block (wosize <= BF_NUM_SMALL)
   - Blue if it is a large block (BF_NUM_SMALL < wosize)
   The block may be left out or the set, depending on its size and the
   sweeper's state.
   The free list size is updated accordingly.
*/
static void bf_insert_remnant (value v)
{
  mlsize_t wosz = Wosize_val (v);

  if (wosz <= BF_NUM_SMALL){
    CAMLassert (Color_val (v) == Caml_white);
    bf_insert_remnant_small (v);
  }else{
    CAMLassert (Color_val (v) == Caml_blue);
    bf_insert_block ((large_free_block *) v);
    caml_fl_cur_wsz += Whsize_wosize (wosz);
  }
}
/* Insert the block into the free set during sweep. The block must be blue. */
static void bf_insert_sweep (value v)
{
  mlsize_t wosz = Wosize_val (v);
  value next;

  CAMLassert (Color_val (v) == Caml_blue);
  if (wosz <= BF_NUM_SMALL){
    while (1){
      next = *bf_small_fl[wosz].merge;
      if (next == Val_NULL){
        set_map (wosz);
        break;
      }
      if (Bp_val (next) >= Bp_val (v)) break;
      bf_small_fl[wosz].merge = &Next_small (next);
    }
    Next_small (v) = *bf_small_fl[wosz].merge;
    *bf_small_fl[wosz].merge = v;
    bf_small_fl[wosz].merge = &Next_small (v);
  }else{
    bf_insert_block ((large_free_block *) v);
  }
}

/* Remove a given block from the free set. */
static void bf_remove (value v)
{
  mlsize_t wosz = Wosize_val (v);

  CAMLassert (Color_val (v) == Caml_blue);
  if (wosz <= BF_NUM_SMALL){
    while (*bf_small_fl[wosz].merge != v){
      CAMLassert (Bp_val (*bf_small_fl[wosz].merge) < Bp_val (v));
      bf_small_fl[wosz].merge = &Next_small (*bf_small_fl[wosz].merge);
    }
    *bf_small_fl[wosz].merge = Next_small (v);
    if (bf_small_fl[wosz].free == Val_NULL) unset_map (wosz);
  }else{
    large_free_block *b = (large_free_block *) v;
    CAMLassert (bf_is_in_tree (b));
    CAMLassert (b->prev->next == b);
    CAMLassert (b->next->prev == b);
    if (b->isnode){
      large_free_block **p = bf_search (bf_large_wosize (b));
      CAMLassert (*p != NULL);
      if (b->next == b){
        bf_remove_node (p);
      }else{
        large_free_block *n = b->next;
        n->prev = b->prev;
        b->prev->next = n;
        *p = n;
        n->isnode = 1;
        n->left = b->left;
        n->right = b->right;
#ifdef DEBUG
        Field ((value) b, 0) = Debug_free_major;
        b->left = b->right = b->next = b->prev =
          (large_free_block *) Debug_free_major;
#endif
      }
    }else{
      b->prev->next = b->next;
      b->next->prev = b->prev;
    }
  }
}

static void bf_init_merge (void)
{
  mlsize_t i;

  CAML_EV_ALLOC_FLUSH();

  caml_fl_merge = Val_NULL;

  for (i = 1; i <= BF_NUM_SMALL; i++){
    /* At the beginning of each small free list is a segment of remnants
       that were pushed back to the list after splitting. These are white
       and they are not in order. We need to remove them
       from the list for coalescing to work. They
       will be picked up by the sweeping code and inserted in the right
       place in the list.
    */
    value p = bf_small_fl[i].free;
    while (1){
      if (p == Val_NULL){
        unset_map (i);
        break;
      }
      if (Color_val (p) == Caml_blue) break;
      CAMLassert (Color_val (p) == Caml_white);
      caml_fl_cur_wsz -= Whsize_val (p);
      p = Next_small (p);
    }
    bf_small_fl[i].free = p;
    /* Set the merge pointer to its initial value */
    bf_small_fl[i].merge = &bf_small_fl[i].free;
  }
}

static void bf_init (void)
{
  mlsize_t i;

  for (i = 1; i <= BF_NUM_SMALL; i++){
    bf_small_fl[i].free = Val_NULL;
    bf_small_fl[i].merge = &bf_small_fl[i].free;
  }
  bf_small_map = 0;
  bf_large_tree = NULL;
  bf_large_least = NULL;
  caml_fl_cur_wsz = 0;
}

/* Make sure all free blocks are blue and tear down the BF data structures. */
static void bf_reset (void)
{
  mlsize_t i;

  for (i = 1; i <= BF_NUM_SMALL; i++){
    /* At the beginning of each small free list is a segment of remnants
       that were pushed back to the list after splitting. These are white
       and they are not in order. We must make them blue before we can
       compact or change the allocator policy.
    */
    value p = bf_small_fl[i].free;
    while (1){
      if (p == Val_NULL || Color_val (p) == Caml_blue) break;
      CAMLassert (Color_val (p) == Caml_white);
      Hd_val (p) = Bluehd_hd (Hd_val (p));
      p = Next_small (p);
    }
  }
  /* We have no malloced data structures, so we can just call [bf_init] to
     clear all our pointers. */
  bf_init ();
}

static header_t *bf_merge_block (value bp, char *limit)
{
  value start;
  value cur;
  mlsize_t wosz;

  CAMLassert (Color_val (bp) == Caml_white);
  /* Find the starting point of the current run of free blocks. */
  if (caml_fl_merge != Val_NULL && Next_in_mem (caml_fl_merge) == bp
      && Color_val (caml_fl_merge) == Caml_blue){
    start = caml_fl_merge;
    bf_remove (start);
  }else{
    start = bp;
  }
  cur = bp;
  while (1){
    /* This slightly convoluted loop is just going over the run of
       white or blue blocks, doing the right thing for each color, and
       stopping on a gray or black block or when limit is passed.
       It is convoluted because we start knowing that the first block
       is white. */
  white:
    if (Tag_val (cur) == Custom_tag){
      void (*final_fun)(value) = Custom_ops_val(cur)->finalize;
      if (final_fun != NULL) final_fun(cur);
    }
    caml_fl_cur_wsz += Whsize_val (cur);
  next:
    caml_prefetch(Hp_val(cur + 4096));
    cur = Next_in_mem (cur);
    if (Hp_val (cur) >= (header_t *) limit){
      CAMLassert (Hp_val (cur) == (header_t *) limit);
      goto end_of_run;
    }
    switch (Color_val (cur)){
    case Caml_white: goto white;
    case Caml_blue: bf_remove (cur); goto next;
    case Caml_black:
      goto end_of_run;
    }
  }
 end_of_run:
  wosz = Wosize_whsize ((value *) cur - (value *) start);
#ifdef DEBUG
  {
    value *p;
    for (p = (value *) start; p < (value *) Hp_val (cur); p++){
      *p = Debug_free_major;
    }
  }
#endif
  while (wosz > Max_wosize){
    Hd_val (start) = Make_header (Max_wosize, 0, Caml_blue);
    bf_insert_sweep (start);
    start = Next_in_mem (start);
    wosz -= Whsize_wosize (Max_wosize);
  }
  if (wosz > 0){
    Hd_val (start) = Make_header (wosz, 0, Caml_blue);
    bf_insert_sweep (start);
  }else{
    Hd_val (start) = Make_header (0, 0, Caml_white);
    caml_fl_cur_wsz -= Whsize_wosize (0);
  }
  FREELIST_DEBUG_bf_check ();
  return Hp_val (cur);
}

static void bf_make_free_blocks (value *p, mlsize_t size, int do_merge,
                                 int color)
{
  mlsize_t sz, wosz;

  while (size > 0){
    if (size > Whsize_wosize (Max_wosize)){
      sz = Whsize_wosize (Max_wosize);
    }else{
      sz = size;
    }
    wosz = Wosize_whsize (sz);
    if (do_merge){
      if (wosz <= BF_NUM_SMALL){
        color = Caml_white;
      }else{
        color = Caml_blue;
      }
      *(header_t *)p = Make_header (wosz, 0, color);
      bf_insert_remnant (Val_hp (p));
    }else{
      *(header_t *)p = Make_header (wosz, 0, color);
    }
    size -= sz;
    p += sz;
  }
}

/********************* exported functions *****************************/

/* Initialize the merge_block machinery (at start of sweeping). */
void (*caml_fl_p_init_merge) (void) = NULL;

/* These are called internally. */
static void (*caml_fl_p_init) (void) = NULL;
static void (*caml_fl_p_reset) (void) = NULL;

/* [caml_fl_merge_block] returns the head pointer of the next block after [bp],
   because merging blocks may change the size of [bp]. */
header_t *(*caml_fl_p_merge_block) (value bp, char *limit) = NULL;

/* Cut a block of memory into pieces of size [Max_wosize], give them headers,
   and optionally merge them into the free list.
   arguments:
   p: pointer to the first word of the block
   size: size of the block (in words)
   do_merge: 1 -> do merge; 0 -> do not merge
   color: which color to give to the pieces; if [do_merge] is 1, this
          is overridden by the merge code, but we have historically used
          [Caml_white].
*/
void (*caml_fl_p_make_free_blocks)
  (value *p, mlsize_t size, int do_merge, int color)
  = NULL;

#ifdef DEBUG
void (*caml_fl_p_check) (void) = NULL;
#endif

/* This variable and the above function pointers must be initialized with
   a call to [caml_set_allocation_policy]. */
uintnat caml_allocation_policy = 999;

void caml_set_allocation_policy (uintnat p)
{
  switch (p){
  case caml_policy_next_fit:
    caml_allocation_policy = p;
    caml_fl_p_init_merge = &nf_init_merge;
    caml_fl_p_reset = &nf_reset;
    caml_fl_p_init = &nf_init;
    caml_fl_p_merge_block = &nf_merge_block;
    caml_fl_p_make_free_blocks = &nf_make_free_blocks;
#ifdef DEBUG
    caml_fl_p_check = &nf_check;
#endif
    break;

  case caml_policy_first_fit:
    caml_allocation_policy = p;
    caml_fl_p_init_merge = &ff_init_merge;
    caml_fl_p_reset = &ff_reset;
    caml_fl_p_init = &ff_init;
    caml_fl_p_merge_block = &ff_merge_block;
    caml_fl_p_make_free_blocks = &ff_make_free_blocks;
#ifdef DEBUG
    caml_fl_p_check = &ff_check;
#endif
    break;

  default:
  case caml_policy_best_fit:
    caml_allocation_policy = caml_policy_best_fit;
    caml_fl_p_init_merge = &bf_init_merge;
    caml_fl_p_reset = &bf_reset;
    caml_fl_p_init = &bf_init;
    caml_fl_p_merge_block = &bf_merge_block;
    caml_fl_p_make_free_blocks = &bf_make_free_blocks;
#ifdef DEBUG
    caml_fl_p_check = &bf_check;
#endif
    break;
  }
}

/* This is called by caml_compact_heap. */
void caml_fl_reset_and_switch_policy (intnat new_allocation_policy)
{
  /* reset the fl data structures */
  (*caml_fl_p_reset) ();
  if (new_allocation_policy != -1){
    caml_set_allocation_policy (new_allocation_policy);
    (*caml_fl_p_init) (); /* initialize the new allocation policy */
  }
}
