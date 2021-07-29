#include "sse_float.h"

uint32_t fp_add32_result (uint32_t m, uint32_t a, uint32_t b)
{
  fp32 r = fp_add32 (m, a, b);
  return r.result;
}

uint32_t fp_add32_mxcsr (uint32_t m, uint32_t a, uint32_t b)
{
  fp32 r = fp_add32 (m, a, b);
  return r.mxcsr;
}

uint32_t fp_sub32_result (uint32_t m, uint32_t a, uint32_t b)
{
  fp32 r = fp_sub32 (m, a, b);
  return r.result;
}

uint32_t fp_sub32_mxcsr (uint32_t m, uint32_t a, uint32_t b)
{
  fp32 r = fp_sub32 (m, a, b);
  return r.mxcsr;
}

uint32_t fp_mul32_result (uint32_t m, uint32_t a, uint32_t b)
{
  fp32 r = fp_mul32 (m, a, b);
  return r.result;
}

uint32_t fp_mul32_mxcsr (uint32_t m, uint32_t a, uint32_t b)
{
  fp32 r = fp_mul32 (m, a, b);
  return r.mxcsr;
}

uint32_t fp_div32_result (uint32_t m, uint32_t a, uint32_t b)
{
  fp32 r = fp_div32 (m, a, b);
  return r.result;
}

uint32_t fp_div32_mxcsr (uint32_t m, uint32_t a, uint32_t b)
{
  fp32 r = fp_div32 (m, a, b);
  return r.mxcsr;
}

uint32_t fp_sqrt32_result (uint32_t m, uint32_t a)
{
  fp32 r = fp_sqrt32 (m, a);
  return r.result;
}

uint32_t fp_sqrt32_mxcsr (uint32_t m, uint32_t a)
{
  fp32 r = fp_sqrt32 (m, a);
  return r.mxcsr;
}

uint32_t fp_fma32_result (uint32_t m, uint32_t a, uint32_t b, uint32_t c)
{
  fp32 r = fp_fma32 (m, a, b, c);
  return r.result;
}

uint32_t fp_fma32_mxcsr (uint32_t m, uint32_t a, uint32_t b, uint32_t c)
{
  fp32 r = fp_fma32 (m, a, b, c);
  return r.mxcsr;
}

uint32_t fp_fms32_result (uint32_t m, uint32_t a, uint32_t b, uint32_t c)
{
  fp32 r = fp_fms32 (m, a, b, c);
  return r.result;
}

uint32_t fp_fms32_mxcsr (uint32_t m, uint32_t a, uint32_t b, uint32_t c)
{
  fp32 r = fp_fms32 (m, a, b, c);
  return r.mxcsr;
}

uint64_t fp_add64_result (uint32_t m, uint64_t a, uint64_t b)
{
  fp64 r = fp_add64 (m, a, b);
  return r.result;
}

uint64_t fp_add64_mxcsr (uint32_t m, uint64_t a, uint64_t b)
{
  fp64 r = fp_add64 (m, a, b);
  return r.mxcsr;
}

uint64_t fp_sub64_result (uint32_t m, uint64_t a, uint64_t b)
{
  fp64 r = fp_sub64 (m, a, b);
  return r.result;
}

uint64_t fp_sub64_mxcsr (uint32_t m, uint64_t a, uint64_t b)
{
  fp64 r = fp_sub64 (m, a, b);
  return r.mxcsr;
}

uint64_t fp_mul64_result (uint32_t m, uint64_t a, uint64_t b)
{
  fp64 r = fp_mul64 (m, a, b);
  return r.result;
}

uint64_t fp_mul64_mxcsr (uint32_t m, uint64_t a, uint64_t b)
{
  fp64 r = fp_mul64 (m, a, b);
  return r.mxcsr;
}

uint64_t fp_div64_result (uint32_t m, uint64_t a, uint64_t b)
{
  fp64 r = fp_div64 (m, a, b);
  return r.result;
}

uint64_t fp_div64_mxcsr (uint32_t m, uint64_t a, uint64_t b)
{
  fp64 r = fp_div64 (m, a, b);
  return r.mxcsr;
}

uint64_t fp_sqrt64_result (uint32_t m, uint64_t a)
{
  fp64 r = fp_sqrt64 (m, a);
  return r.result;
}

uint64_t fp_sqrt64_mxcsr (uint32_t m, uint64_t a)
{
  fp64 r = fp_sqrt64 (m, a);
  return r.mxcsr;
}

uint64_t fp_fma64_result (uint32_t m, uint64_t a, uint64_t b, uint64_t c)
{
  fp64 r = fp_fma64 (m, a, b, c);
  return r.result;
}

uint64_t fp_fma64_mxcsr (uint32_t m, uint64_t a, uint64_t b, uint64_t c)
{
  fp64 r = fp_fma64 (m, a, b, c);
  return r.mxcsr;
}

uint64_t fp_fms64_result (uint32_t m, uint64_t a, uint64_t b, uint64_t c)
{
  fp64 r = fp_fms64 (m, a, b, c);
  return r.result;
}

uint64_t fp_fms64_mxcsr (uint32_t m, uint64_t a, uint64_t b, uint64_t c)
{
  fp64 r = fp_fms64 (m, a, b, c);
  return r.mxcsr;
}

uint32_t fp64_to_fp32_result (uint32_t m, uint64_t a)
{
  fp32 r = fp64_to_fp32 (m, a);
  return r.result;
}

uint32_t fp64_to_fp32_mxcsr (uint32_t m, uint64_t a)
{
  fp32 r = fp64_to_fp32 (m, a);
  return r.mxcsr;
}
