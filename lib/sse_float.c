#include "sse_float.h"

// ------------------------------------------------------------
// Test for availability of Fused Multiply Add (FMA) extension.
// Intoduced with 4th-generation Intel processors (Haswell).
// ------------------------------------------------------------
uint32_t has_fma()
{
   uint32_t res;

   __asm__ ( "mov $1, %%eax;"
             "cpuid;"
             "and $0x18001000, %%ecx;"
             "cmp $0x18001000, %%ecx;"
             "jne not_supported%=;"
             "mov $0, %%ecx;"
             "xgetbv;"
             "and $6, %%eax;"
             "cmp $6, %%eax;"
             "jne not_supported%=;"
             "mov $1, %%eax;"
             "jmp done%=;"
             "not_supported%=: mov $0, %%eax;"
             "done%=:;"
             : "=a" (res) ::);

   return res;
}

// ------------------------------------------------------------
// Read the MXCSR status register
// ------------------------------------------------------------
uint32_t get_mxcsr()
{
    uint32_t mxcsr;

    __asm__ ("stmxcsr %0" : : "m" (mxcsr));

    return mxcsr;
}

// ------------------------------------------------------------
// Set the MXCSR status register
// ------------------------------------------------------------
void set_mxcsr(uint32_t mxcsr)
{
    __asm__ ("ldmxcsr %0" : : "m" (mxcsr));
}

// ------------------------------------------------------------
// Reset MXCSR and set the rounding mode bits to "mode".
// 0b00 (NEAREST), 0b01 (NEGINF), 0b10 (POSINF), 0b11 (ZERO)
// ------------------------------------------------------------
void set_round_mode(uint32_t mode)
{
    set_mxcsr( 0x1F80 | ((mode & 0b11) << 13) );
}

// uint32_t get_round_mode() { return ((get_mxcsr() >> 13) & 0b11); }

// ------------------------------------------------------------
// 32-bit Addition
// ------------------------------------------------------------
fp32 fp_add32 (uint32_t mode, uint32_t a, uint32_t b)
{
    fp32 out;

    set_round_mode (mode);

    __asm__ ( "movss %2, %%xmm0;"
              "movss %3, %%xmm1;"
              "addss %%xmm1, %%xmm0;"
              "movss %%xmm0, %0;"
              "stmxcsr %1;"
            : "=m" (out.result), "=m" (out.mxcsr)
            : "m" (a), "m" (b)
            );

    return out;
}

// ------------------------------------------------------------
// 64-bit Addition
// ------------------------------------------------------------
fp64 fp_add64 (uint32_t mode, uint64_t a, uint64_t b)
{
    fp64 out;

    set_round_mode (mode);

    __asm__ ( "movsd %2, %%xmm0;"
              "movsd %3, %%xmm1;"
              "addsd %%xmm1, %%xmm0;"
              "movsd %%xmm0, %0;"
              "stmxcsr %1;"
            : "=m" (out.result), "=m" (out.mxcsr)
            : "m" (a), "m" (b)
            );

    return out;
}

// ------------------------------------------------------------
// 32-bit Subtraction
// ------------------------------------------------------------
fp32 fp_sub32 (uint32_t mode, uint32_t a, uint32_t b)
{
    fp32 out;

    set_round_mode (mode);

    __asm__ ( "movss %2, %%xmm0;"
              "movss %3, %%xmm1;"
              "subss %%xmm1, %%xmm0;"
              "movss %%xmm0, %0;"
              "stmxcsr %1;"
            : "=m" (out.result), "=m" (out.mxcsr)
            : "m" (a), "m" (b)
            );

    return out;
}

// ------------------------------------------------------------
// 64-bit Subtraction
// ------------------------------------------------------------
fp64 fp_sub64 (uint32_t mode, uint64_t a, uint64_t b)
{
    fp64 out;

    set_round_mode (mode);

    __asm__ ( "movsd %2, %%xmm0;"
              "movsd %3, %%xmm1;"
              "subsd %%xmm1, %%xmm0;"
              "movsd %%xmm0, %0;"
              "stmxcsr %1;"
            : "=m" (out.result), "=m" (out.mxcsr)
            : "m" (a), "m" (b)
            );

    return out;
}

// ------------------------------------------------------------
// 32-bit Multiplication
// ------------------------------------------------------------
fp32 fp_mul32 (uint32_t mode, uint32_t a, uint32_t b)
{
    fp32 out;

    set_round_mode (mode);

    __asm__ ( "movss %2, %%xmm0;"
              "movss %3, %%xmm1;"
              "mulss %%xmm1, %%xmm0;"
              "movss %%xmm0, %0;"
              "stmxcsr %1;"
            : "=m" (out.result), "=m" (out.mxcsr)
            : "m" (a), "m" (b)
            );

    return out;
}

// ------------------------------------------------------------
// 64-bit Multiplication
// ------------------------------------------------------------
fp64 fp_mul64 (uint32_t mode, uint64_t a, uint64_t b)
{
    fp64 out;

    set_round_mode (mode);

    __asm__ ( "movsd %2, %%xmm0;"
              "movsd %3, %%xmm1;"
              "mulsd %%xmm1, %%xmm0;"
              "movsd %%xmm0, %0;"
              "stmxcsr %1;"
            : "=m" (out.result), "=m" (out.mxcsr)
            : "m" (a), "m" (b)
            );

    return out;
}

// ------------------------------------------------------------
// 32-bit Division
// ------------------------------------------------------------
fp32 fp_div32 (uint32_t mode, uint32_t a, uint32_t b)
{
    fp32 out;

    set_round_mode (mode);

    __asm__ ( "movss %2, %%xmm0;"
              "movss %3, %%xmm1;"
              "divss %%xmm1, %%xmm0;"
              "movss %%xmm0, %0;"
              "stmxcsr %1;"
            : "=m" (out.result), "=m" (out.mxcsr)
            : "m" (a), "m" (b)
            );

    return out;
}

// ------------------------------------------------------------
// 64-bit Division
// ------------------------------------------------------------
fp64 fp_div64 (uint32_t mode, uint64_t a, uint64_t b)
{
    fp64 out;

    set_round_mode (mode);

    __asm__ ( "movsd %2, %%xmm0;"
              "movsd %3, %%xmm1;"
              "divsd %%xmm1, %%xmm0;"
              "movsd %%xmm0, %0;"
              "stmxcsr %1;"
            : "=m" (out.result), "=m" (out.mxcsr)
            : "m" (a), "m" (b)
            );

    return out;
}

// ------------------------------------------------------------
// 32-bit Square Root
// ------------------------------------------------------------
fp32 fp_sqrt32 (uint32_t mode, uint32_t a)
{
    fp32 out;

    set_round_mode (mode);

    __asm__ ( "movss %2, %%xmm0;"
              "sqrtss %%xmm0, %%xmm0;"
              "movss %%xmm0, %0;"
              "stmxcsr %1;"
            : "=m" (out.result), "=m" (out.mxcsr)
            : "m" (a)
            );

    return out;
}

// ------------------------------------------------------------
// 64-bit Square Root
// ------------------------------------------------------------
fp64 fp_sqrt64 (uint32_t mode, uint64_t a)
{
    fp64 out;

    set_round_mode (mode);

    __asm__ ( "movsd %2, %%xmm0;"
              "sqrtsd %%xmm0, %%xmm0;"
              "movsd %%xmm0, %0;"
              "stmxcsr %1;"
            : "=m" (out.result), "=m" (out.mxcsr)
            : "m" (a)
            );

    return out;
}

// ------------------------------------------------------------
// 32-bit Fused Multipy Add (requires has_fma() == 1)
// ------------------------------------------------------------
fp32 fp_fma32 (uint32_t mode, uint32_t a, uint32_t b, uint32_t c)
{
    fp32 out;

    set_round_mode (mode);

    __asm__ ( "movss %4, %%xmm0;"
              "movss %2, %%xmm1;"
              "movss %3, %%xmm2;"
              "vfmadd231ss %%xmm1, %%xmm2, %%xmm0;"
              "movss %%xmm0, %0;"
              "stmxcsr %1;"
            : "=m" (out.result), "=m" (out.mxcsr)
            : "m" (a), "m" (b), "m" (c)
            );

    return out;
}

// ------------------------------------------------------------
// 64-bit Fused Multipy Add (requires has_fma() == 1)
// ------------------------------------------------------------
fp64 fp_fma64 (uint32_t mode, uint64_t a, uint64_t b, uint64_t c)
{
    fp64 out;

    set_round_mode (mode);

    __asm__ ( "movsd %4, %%xmm0;"
              "movsd %2, %%xmm1;"
              "movsd %3, %%xmm2;"
              "vfmadd231sd %%xmm1, %%xmm2, %%xmm0;"
              "movsd %%xmm0, %0;"
              "stmxcsr %1;"
            : "=m" (out.result), "=m" (out.mxcsr)
            : "m" (a), "m" (b), "m" (c)
            );

    return out;
}

// ------------------------------------------------------------
// 32-bit Fused Multipy Sub (requires has_fma() == 1)
// ------------------------------------------------------------
fp32 fp_fms32 (uint32_t mode, uint32_t a, uint32_t b, uint32_t c)
{
    fp32 out;

    set_round_mode (mode);

    __asm__ ( "movss %4, %%xmm0;"
              "movss %2, %%xmm1;"
              "movss %3, %%xmm2;"
              "vfmsub231ss %%xmm1, %%xmm2, %%xmm0;"
              "movss %%xmm0, %0;"
              "stmxcsr %1;"
            : "=m" (out.result), "=m" (out.mxcsr)
            : "m" (a), "m" (b), "m" (c)
            );

    return out;
}

// ------------------------------------------------------------
// 64-bit Fused Multipy Sub (requires has_fma() == 1)
// ------------------------------------------------------------
fp64 fp_fms64 (uint32_t mode, uint64_t a, uint64_t b, uint64_t c)
{
    fp64 out;

    set_round_mode (mode);

    __asm__ ( "movsd %4, %%xmm0;"
              "movsd %2, %%xmm1;"
              "movsd %3, %%xmm2;"
              "vfmsub231sd %%xmm1, %%xmm2, %%xmm0;"
              "movsd %%xmm0, %0;"
              "stmxcsr %1;"
            : "=m" (out.result), "=m" (out.mxcsr)
            : "m" (a), "m" (b), "m" (c)
            );

    return out;
}

// ------------------------------------------------------------
// 32-bit Compare Equal
// ------------------------------------------------------------
uint32_t fp_cmpeq32 (uint32_t a, uint32_t b)
{
    uint32_t out;

    __asm__ ( "movss %1, %%xmm0;"
              "movss %2, %%xmm1;"
              "cmpss $0x0, %%xmm1, %%xmm0;"
              "movss %%xmm0, %0;"
            : "=m" (out)
            : "m" (a), "m" (b)
            );

    return out;
}

// ------------------------------------------------------------
// 64-bit Compare Equal
// ------------------------------------------------------------
uint64_t fp_cmpeq64 (uint64_t a, uint64_t b)
{
    uint64_t out;

    __asm__ ( "movsd %1, %%xmm0;"
              "movsd %2, %%xmm1;"
              "cmpsd $0x0, %%xmm1, %%xmm0;"
              "movsd %%xmm0, %0;"
            : "=m" (out)
            : "m" (a), "m" (b)
            );

    return out;
}

// ------------------------------------------------------------
// 32-bit Compare Less-Than
// ------------------------------------------------------------
uint32_t fp_cmplt32 (uint32_t a, uint32_t b)
{
    uint32_t out;

    __asm__ ( "movss %1, %%xmm0;"
              "movss %2, %%xmm1;"
              "cmpss $0x11, %%xmm1, %%xmm0;"
              "movss %%xmm0, %0;"
            : "=m" (out)
            : "m" (a), "m" (b)
            );

    return out;
}

// ------------------------------------------------------------
// 64-bit Compare Less-Than
// ------------------------------------------------------------
uint64_t fp_cmplt64 (uint64_t a, uint64_t b)
{
    uint64_t out;

    __asm__ ( "movsd %1, %%xmm0;"
              "movsd %2, %%xmm1;"
              "cmpsd $0x11, %%xmm1, %%xmm0;"
              "movsd %%xmm0, %0;"
            : "=m" (out)
            : "m" (a), "m" (b)
            );

    return out;
}

// ------------------------------------------------------------
// 32-bit Compare Less-Equal
// ------------------------------------------------------------
uint32_t fp_cmple32 (uint32_t a, uint32_t b)
{
    uint32_t out;

    __asm__ ( "movss %1, %%xmm0;"
              "movss %2, %%xmm1;"
              "cmpss $0x12, %%xmm1, %%xmm0;"
              "movss %%xmm0, %0;"
            : "=m" (out)
            : "m" (a), "m" (b)
            );

    return out;
}
// ------------------------------------------------------------
// 64-bit Compare Less-Equal
// ------------------------------------------------------------
uint64_t fp_cmple64 (uint64_t a, uint64_t b)
{
    uint64_t out;

    __asm__ ( "movsd %1, %%xmm0;"
              "movsd %2, %%xmm1;"
              "cmpsd $0x12, %%xmm1, %%xmm0;"
              "movsd %%xmm0, %0;"
            : "=m" (out)
            : "m" (a), "m" (b)
            );

    return out;
}

// ------------------------------------------------------------
// 32-bit Round to integer
// ------------------------------------------------------------
uint32_t fp_roundtoint32 (uint32_t mode, uint32_t a)
{
    uint32_t out;

    switch (mode) {

      case 0b01:

          __asm__ ( "movss %1, %%xmm0;"
                    "roundss $1, %%xmm0, %%xmm0;"
                    "movss %%xmm0, %0;"
                  : "=m" (out)
                  : "m" (a)
                  );
          break;

      case 0b10:

          __asm__ ( "movss %1, %%xmm0;"
                    "roundss $2, %%xmm0, %%xmm0;"
                    "movss %%xmm0, %0;"
                  : "=m" (out)
                  : "m" (a)
                  );
          break;

      case 0b11:

          __asm__ ( "movss %1, %%xmm0;"
                    "roundss $3, %%xmm0, %%xmm0;"
                    "movss %%xmm0, %0;"
                  : "=m" (out)
                  : "m" (a)
                  );
          break;

      default:

          __asm__ ( "movss %1, %%xmm0;"
                    "roundss $0, %%xmm0, %%xmm0;"
                    "movss %%xmm0, %0;"
                  : "=m" (out)
                  : "m" (a)
                  );
          break;

    }

    return out;
}

// ------------------------------------------------------------
// 64-bit Round to integer
// ------------------------------------------------------------
uint64_t fp_roundtoint64 (uint32_t mode, uint64_t a)
{
    uint64_t out;

    switch (mode) {

      case 0b01:

          __asm__ ( "movsd %1, %%xmm0;"
                    "roundsd $1, %%xmm0, %%xmm0;"
                    "movsd %%xmm0, %0;"
                  : "=m" (out)
                  : "m" (a)
                  );
          break;

      case 0b10:

          __asm__ ( "movsd %1, %%xmm0;"
                    "roundsd $2, %%xmm0, %%xmm0;"
                    "movsd %%xmm0, %0;"
                  : "=m" (out)
                  : "m" (a)
                  );
          break;

      case 0b11:

          __asm__ ( "movsd %1, %%xmm0;"
                    "roundsd $3, %%xmm0, %%xmm0;"
                    "movsd %%xmm0, %0;"
                  : "=m" (out)
                  : "m" (a)
                  );
          break;

      default:

          __asm__ ( "movsd %1, %%xmm0;"
                    "roundsd $0, %%xmm0, %%xmm0;"
                    "movsd %%xmm0, %0;"
                  : "=m" (out)
                  : "m" (a)
                  );
          break;

    }

    return out;
}

// ------------------------------------------------------------
// 32-bit Convert to integer
// ------------------------------------------------------------
uint64_t fp_toint32 (uint32_t mode, uint32_t a)
{
    uint64_t out;

    set_round_mode (mode);

    __asm__ ( "movss %1, %%xmm0;"
              "cvtss2si %%xmm0, %%rax;"
            : "=a" (out)
            : "m" (a)
            );

    return out;
}

// ------------------------------------------------------------
// 64-bit Convert to integer
// ------------------------------------------------------------
uint64_t fp_toint64 (uint32_t mode, uint64_t a)
{
    uint64_t out;

    set_round_mode (mode);

    __asm__ ( "movsd %1, %%xmm0;"
              "cvtsd2si %%xmm0, %%rax;"
            : "=a" (out)
            : "m" (a)
            );

    return out;
}

// ------------------------------------------------------------
// 32-bit Convert from integer
// ------------------------------------------------------------
uint32_t fp_fromint32 (uint32_t mode, uint64_t a)
{
    uint32_t out;

    set_round_mode (mode);

    __asm__ ( "movq %1, %%rax;"
              "cvtsi2ss %%rax, %%xmm0;"
              "movss %%xmm0, %0;"
            : "=m" (out)
            : "g" (a)
            );

    return out;
}

// ------------------------------------------------------------
// 64-bit Convert from integer
// ------------------------------------------------------------
uint64_t fp_fromint64 (uint32_t mode, uint64_t a)
{
    uint64_t out;

    set_round_mode (mode);

    __asm__ ( "movq %1, %%rax;"
              "cvtsi2sd %%rax, %%xmm0;"
              "movsd %%xmm0, %0;"
            : "=m" (out)
            : "g" (a)
            );

    return out;
}

// ------------------------------------------------------------
// 32-bit to 64-bit
// ------------------------------------------------------------
uint64_t fp32_to_fp64 (uint32_t a)
{
    uint64_t out;

    __asm__ ( "movss %1, %%xmm0;"
              "cvtss2sd %%xmm0, %%xmm1;"
              "movsd %%xmm1, %0;"
            : "=m" (out)
            : "m" (a)
            );

    return out;
}

// ------------------------------------------------------------
// 64-bit to 32-bit with flags
// ------------------------------------------------------------
fp32 fp64_to_fp32 (uint32_t mode, uint64_t a)
{
    fp32 out;

    set_round_mode (mode);

    __asm__ ( "movsd %2, %%xmm0;"
              "cvtsd2ss %%xmm0, %%xmm1;"
              "movss %%xmm1, %0;"
              "stmxcsr %1;"
            : "=m" (out.result), "=m" (out.mxcsr)
            : "m" (a)
            );

    return out;
}

// ------------------------------------------------------------
// 32-bit From string
// ------------------------------------------------------------
uint32_t fp_fromstring32 (char* s)
{
  char *ptr;

  set_round_mode (0b00);

  float d = strtof (s, &ptr);

  return *((uint32_t*) &d);
}

// ------------------------------------------------------------
// 32-bit Rest from string
// ------------------------------------------------------------
char* fp_restfromstring32 (char* s)
{
  char *ptr;

  strtof (s, &ptr);

  return ptr;
}

// ------------------------------------------------------------
// 64-bit From string
// ------------------------------------------------------------
uint64_t fp_fromstring64 (char* s)
{
  char *ptr;

  set_round_mode (0b00);

  double d = strtod (s, &ptr);

  return *((uint64_t*) &d);
}

// ------------------------------------------------------------
// 64-bit Rest from string
// ------------------------------------------------------------
char* fp_restfromstring64 (char* s)
{
  char *ptr;

  strtod (s, &ptr);

  return ptr;
}

