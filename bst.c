#include <stddef.h>

extern void * malloc(size_t n); // Why not include stdlib?

// TODO: Generalize `int` to `void *` (will require a function pointer to compare elements for search)
struct bst {
  int key;
  int val;
  struct bst * left;
  struct bst * right;
};

struct bst * new_bst(int key, int val) {
  struct bst * bst;
  bst = (struct bst *) malloc(sizeof(struct bst));
  bst->key = key;
  bst->val = val;
  bst->left = NULL;
  bst->right = NULL;
  return bst;
}

struct bst * search_bst(struct bst * bst, int key) {
  for (;;) {
    if (!bst)
      return bst;
    else if (key == bst->key)
      return bst;
    else if (key < bst->key)
      bst = bst->left;
    else 
      bst = bst->right;
  }
}

void insert_bst(struct bst ** bst, int key, int val) {
  // if (!bst) return; // Is this necessary? Don't we assume bst<>nullval in the spec? (Implicitly through the data_at).
  // else
  for (;;) {
    if (!(*bst)) {
      *bst = new_bst(key, val);
      return;
    }
    else if (key == (*bst)->key) {
      (*bst)->val = val;
      return;
    }
    else if (key < (*bst)->key)
      bst = &(*bst)->left;
    else
      bst = &(*bst)->right;
  }
}

// TODO: Delete

// TODO: Free

// TODO: Merge?
