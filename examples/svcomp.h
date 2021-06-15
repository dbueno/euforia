#include <stddef.h>
#include <stdint.h>

extern void __VERIFIER_error(void) __attribute__ ((__noreturn__));
#define __VERIFIER_assert(c) if (!(c)) __VERIFIER_error()

extern int __VERIFIER_nondet_bool(void);
extern char __VERIFIER_nondet_char(void);
extern int __VERIFIER_nondet_int(void);
extern float __VERIFIER_nondet_float(void);
extern double __VERIFIER_nondet_double(void);
extern long __VERIFIER_nondet_long(void);
extern void *__VERIFIER_nondet_pointer(void);
extern short __VERIFIER_nondet_short(void);
extern size_t __VERIFIER_nondet_size_t(void);
extern uint32_t __VERIFIER_nondet_u32(void);
extern unsigned char __VERIFIER_nondet_uchar(void);
extern unsigned int __VERIFIER_nondet_uint(void);
extern unsigned long __VERIFIER_nondet_ulong(void);
extern unsigned __VERIFIER_nondet_unsigned(void);
extern unsigned short __VERIFIER_nondet_ushort(void);

extern void __VERIFIER_assume(int);

extern void __VERIFIER_printf(const char *fmt, ...) __attribute__ ((format (printf, 1, 2)));
