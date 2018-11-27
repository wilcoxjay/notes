#include <stdio.h>
#include <stdlib.h>

typedef unsigned int uint;

enum tag { THUNK, VALUE };

struct LList {
  enum tag tag;
  union {
    struct {
      uint data;
      struct LList* next;
    };
    struct {
      void* env;
      void (*thunk)(void* env, struct LList* dst);
    };
  };
};

void force(struct LList* ll) {
  if (ll->tag == THUNK) {
    ll->thunk(ll->env, ll);
  }
}

// force up to n values at front of list
void take(struct LList* ll, uint n) {
  while (n-- > 0 && ll != NULL) {
    force(ll);
    ll = ll->next;
  }
}

void print_until_thunk(struct LList* ll) {
  while (ll != NULL && ll->tag == VALUE) {
    printf("%u", (int)ll->data);
    ll = ll->next;
  }
}

// ---------------------------------

void nats_thunk(void* env, struct LList* dst) {
  dst->tag = VALUE;
  dst->data = (uint)env;
  dst->next = malloc(sizeof(struct LList));
  dst->next->tag = THUNK;
  dst->next->env = env + 1;
  dst->next->thunk = nats_thunk;
}

struct LList* nats() {
  struct LList* ans = malloc(sizeof(struct LList));
  ans->tag = THUNK;
  ans->env = 0;
  ans->thunk = nats_thunk;
  return ans;
}

int main(void) {
  struct LList* ns = nats();
  take(ns, 10);
  print_until_thunk(ns);
  printf("\n");

  return 0;
}


