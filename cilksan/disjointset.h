/* -*- Mode: C++ -*- */

#ifndef _DISJOINTSET_H
#define _DISJOINTSET_H

#include <assert.h>
#include <cstdio>
#include <cstdlib>
#include <stdint.h>
#include "list.h"
#include "debug_util.h"

extern List_t disjoint_set_list;

template <typename DISJOINTSET_DATA_T>
class DisjointSet_t {
private:
  // the node that initialized this set; const field that does not change  
  DISJOINTSET_DATA_T const _node; 
  // the oldest node representing the set that the _node belongs to 
  DISJOINTSET_DATA_T _set_node; 
  DisjointSet_t *_set_parent;
  uint64_t _rank; // roughly as the height of this node

  int64_t _ref_count;

  // HACK: The destructor calls a callback to free the set node, but in order
  // for that callback to get the set node, it needs to call find_set which has
  // assertions for ref counts. Thus, we don't dec our ref count if we're
  // destructing.
  bool _destructing;

  void assert_not_freed() {
    if (!(_destructing || _ref_count >= 0))
      // fprintf(stderr, "%p->assert_not_freed(): _destructing = %d, _ref_count = %ld\n",
      // 	      this, _destructing, _ref_count);
    cilksan_assert(_destructing || _ref_count >= 0);
  }

  /*
   * The only reason we need this function is to ensure that  
   * the _set_node returned for representing this set is the oldest 
   * node in the set.  
   */
  __attribute__((always_inline))
  void swap_set_node_with(DisjointSet_t *that) {
    assert_not_freed();

    DISJOINTSET_DATA_T tmp;
    tmp = this->_set_node;
    this->_set_node = that->_set_node;
    that->_set_node = tmp;
  }

  // Frees the old parent if it has no more references.
  void set_parent(DisjointSet_t *that) {
    // fprintf(stderr, "%p->set_parent(%p), _destructing = %d, _ref_count = %ld\n",
    // 	    this, that, _destructing, _ref_count);
    assert_not_freed();

    DisjointSet_t *old_parent = this->_set_parent;

    this->_set_parent = that;
    that->inc_ref_count();

    // dec_ref_count checks whether a node is its only reference (through
    // parent). If we called dec_ref_count (removing the parent relationship)
    // before setting this's parent and we had another reference besides the
    // parent relationship, dec_ref_count would incorrectly believe that this's
    // only reference is in having itself as a parent.
    if (old_parent != NULL) {
      old_parent->dec_ref_count();
    }
  }

  /*
   * Links this disjoint set to that disjoint set.
   * Don't need to be public.
   *
   * @param that that disjoint set.
   */
  __attribute__((always_inline))
  void link(DisjointSet_t *that) {
    // fprintf(stderr, "%p->link(%p)\n", this, that);
    assert_not_freed();
    cilksan_assert(that != NULL);

    // link the node with smaller height into the node with larger height
    if (this->_rank > that->_rank) {
      that->set_parent(this);
    } else {
      this->set_parent(that);
      if (this->_rank == that->_rank)
	++that->_rank;
      // because we are linking this into the forest rooted at that, let's
      // swap the nodes in this object and that object to keep the metadata
      // hold in the node consistent.
      this->swap_set_node_with(that);
    }
  }

  /*
   * Finds the set containing this disjoint set element.
   *
   * Note: Performs path compression along the way.
   *       The _set_parent field will be updated after the call.
   */
  __attribute__((always_inline))
  DisjointSet_t* find_set() {
    // fprintf(stderr, "%p->find_set()\n", this);
    assert_not_freed();

    disjoint_set_list.lock();
    DisjointSet_t *node = this;

    node->assert_not_freed();

    while (node->_set_parent != node) {
      cilksan_assert(node->_set_parent);

      if (__builtin_expect(!_destructing || node != this, 1)) {
	disjoint_set_list.push(node);
      }
      node = node->_set_parent;
    }

    // node is now the root. Perform path compression by updating the parents
    // of each of the nodes we saw.
    // We process backwards so that in case a node ought to be freed (i.e. its
    // child was the last referencing it), we don't process it after freeing.
    for (int i = disjoint_set_list.length() - 2; i >= 0; i--) {
      DisjointSet_t *p = (DisjointSet_t *)disjoint_set_list.list()[i];
      // We don't need to check that p != p->_set_parent because the root of
      // the set wasn't pushed to the list (see the while loop above).
      p->set_parent(node);
    }

    disjoint_set_list.unlock();
    return node;
  }

public:
  DisjointSet_t(DISJOINTSET_DATA_T node) :
      _node(node),
      _set_node(node),
      _set_parent(NULL),
      _rank(0),
      _ref_count(0),
      _destructing(false) { 
    // fprintf(stderr, "Constructing %p\n", this);
    set_parent(this);
    WHEN_CILKSAN_DEBUG(debug_count++);
  }

#if CILKSAN_DEBUG
  static long debug_count;
  static uint64_t nodes_created;
#endif

  static void (*dtor_callback)(DisjointSet_t *);

  ~DisjointSet_t() {
    // fprintf(stderr, "Destructing %p\n", this);
    _destructing = true;
    dtor_callback(this);
    if (this->_set_parent != this) {
      // Otherwise, we run the risk of double freeing.
      _set_parent->dec_ref_count();
    }

#if CILKSAN_DEBUG
    _destructing = false;
    _set_parent = NULL;
    _ref_count = -1;

    debug_count--;
#endif
  }

  // Decrements the ref count.  Returns true if the node was deleted
  // as a result.
  inline void dec_ref_count() {
    // fprintf(stderr, "%p->dec_ref_count(), _ref_count = %ld\n", this, _ref_count);
    assert_not_freed();

    --_ref_count;
    if (_ref_count == 0 || (_ref_count == 1 && this->_set_parent == this)) {
      delete this;
    }
  }

  inline void inc_ref_count() {
    // fprintf(stderr, "%p->inc_ref_count(), _ref_count = %ld\n", this, _ref_count);
    assert_not_freed();

    ++_ref_count;
  }

  __attribute__((always_inline))
  DISJOINTSET_DATA_T get_node() {
    assert_not_freed();

    return _node;
  }

  __attribute__((always_inline))
  DISJOINTSET_DATA_T get_set_node() {
    assert_not_freed();

    return find_set()->_set_node;
  }

  /*
   * Unions this disjoint set and that disjoint set.
   *
   * NOTE: implicitly, in order to maintain the oldest _set_node, one
   * should always combine younger set into this set (defined by creation
   * time).  Since we union by rank, we may end up linking this set to 
   * the younger set.  To make sure that we always return the oldest _node 
   * to represent the set, we use an additional _set_node field to keep 
   * track of the oldest node and use that to represent the set.
   *
   * @param that that (younger) disjoint set.
   */
  // Called "combine," because "union" is a reserved keyword in C
  void combine(DisjointSet_t *that) {
    // fprintf(stderr, "%p->combine(%p)\n", this, that);
    assert_not_freed();

    cilksan_assert(that);
    cilksan_assert(this->find_set() != that->find_set());
    this->find_set()->link(that->find_set());
    cilksan_assert(this->find_set() == that->find_set());
  }

};

#endif // #ifndef _DISJOINTSET_H
