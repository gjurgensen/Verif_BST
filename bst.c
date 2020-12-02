#include <stddef.h>

extern void * malloc(size_t n);
extern void * free(size_t n);

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

// Assumes a non-empty bst
struct bst pop_min(struct bst ** bst_ptr);

void delete_bst(struct bst ** parent_ptr, int key) {
  struct bst * parent = *parent_ptr;
  if (!parent)
    return;
  else if (key == parent->key) {
    if (parent->left) {
      if (parent->right) {
        struct bst min = pop_min(&(parent->right));
        parent->key = min.key;
        parent->val = min.val;
      }
      else {
        *parent_ptr = parent->left;
        free(parent);
      }
    }
    else {
      if (parent->right) {
        *parent_ptr = parent->right;
        free(parent);
      }
      else {
        free(parent);
        *parent_ptr = (struct bst *)NULL;
      }
      // Move free(parent) to here?
    }
  }
  else {
    // invariant tip: key != parent->key
    for (;;) {
      if (key < parent->key) {
        if (!(parent->left))
          return;
        else if (key == parent->left->key) {
          if (parent->left->left) {
            if (parent->left->right) {
              struct bst min = pop_min(&(parent->left->right));
              parent->left->key = min.key;
              parent->left->val = min.val;
              return;
            }
            else {
              struct bst * del = parent->left;
              parent->left = parent->left->left;
              free(del);
              return;
            }
          }
          else {
            if (parent->left->right) {
              struct bst * del = parent->left;
              parent->left = parent->left->right;
              free(del);
              return;
            }
            else {
              free(parent->left);
              parent->left = (struct bst *)NULL;
              return;
            }
            // free(parent)
          }
          // return;
        }
        else 
          parent = parent->left;
      }
      else {
        if (!(parent->right))
          return;
        if (key == parent->right->key) {
          if (parent->right->left) {
            if (parent->right->right) {
              struct bst min = pop_min(&(parent->right->right));
              parent->right->key = min.key;
              parent->right->val = min.val;
              return;
            }
            else {
              struct bst * del = parent->right;
              parent->right = parent->right->left;
              free(del);
              return;
            }
          }
          else {
            if (parent->right->right) {
              struct bst * del = parent->right;
              parent->right = parent->right->right;
              free(del);
              return;
            }
            else {
              free(parent->right);
              parent->right = (struct bst *)NULL;
              return;
            }
            // free(parent)
          }
          // return;
        }
        else 
          parent = parent->right;
     }
    }
  }
}

// TODO: Free

// TODO: Merge?
