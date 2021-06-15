
extern void __VERIFIER_error() __attribute__ ((__noreturn__));
#define __VERIFIER_assert(c) if (!(c)) __VERIFIER_error();

extern char __VERIFIER_nondet_char(void);
extern int __VERIFIER_nondet_int(void);
extern long __VERIFIER_nondet_long(void);
extern void *__VERIFIER_nondet_pointer(void);
extern int __VERIFIER_nondet_int();


struct node {
  int mark;
  struct node *next;
};

void mark(struct node *list) {
  /* aux vars */
  struct node *h, *hnext;
  h = list; /* TODO should point to any non-null element */
  hnext = h->next;


  struct node *this, *tmp, *prev;
  prev = 0;
  this = list;
  /* traverse list and mark, setting back pointers */
  while (this != 0) {
    if (this->mark == 1)
      break;
    this->mark = 1;
    tmp = prev;
    prev = this;
    this = this->next;
    prev->next = tmp;
  }
  /* traverse back, resetting the pointers */
  while (prev != 0) {
    tmp = this;
    this = prev;
    prev = prev->next;
    this->next = tmp;
  }

  __VERIFIER_assert();
}
