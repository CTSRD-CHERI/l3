#include <stdint.h>
#include <stdlib.h>

typedef struct fp32
{
   uint32_t mxcsr;
   uint32_t result;
} fp32;

typedef struct fp64
{
   uint32_t mxcsr;
   uint64_t result;
} fp64;

uint32_t has_fma ();
uint32_t get_mxcsr ();

fp32 fp_add32 (uint32_t, uint32_t, uint32_t);
fp32 fp_sub32 (uint32_t, uint32_t, uint32_t);
fp32 fp_mul32 (uint32_t, uint32_t, uint32_t);
fp32 fp_div32 (uint32_t, uint32_t, uint32_t);
fp32 fp_sqrt32 (uint32_t, uint32_t);
fp32 fp_fma32 (uint32_t, uint32_t, uint32_t, uint32_t);
fp32 fp_fms32 (uint32_t, uint32_t, uint32_t, uint32_t);
uint32_t fp_cmpeq32 (uint32_t, uint32_t);
uint32_t fp_cmplt32 (uint32_t, uint32_t);
uint32_t fp_cmple32 (uint32_t, uint32_t);
uint32_t fp_roundtoint32 (uint32_t, uint32_t);
uint64_t fp_toint32 (uint32_t, uint32_t);
uint32_t fp_fromint32 (uint32_t, uint64_t);
uint32_t fp_fromstring32 (char*);
char* fp_restfromstring32 (char*);

fp64 fp_add64 (uint32_t, uint64_t, uint64_t);
fp64 fp_sub64 (uint32_t, uint64_t, uint64_t);
fp64 fp_mul64 (uint32_t, uint64_t, uint64_t);
fp64 fp_div64 (uint32_t, uint64_t, uint64_t);
fp64 fp_sqrt64 (uint32_t, uint64_t);
fp64 fp_fma64 (uint32_t, uint64_t, uint64_t, uint64_t);
fp64 fp_fms64 (uint32_t, uint64_t, uint64_t, uint64_t);
uint64_t fp_cmpeq64 (uint64_t, uint64_t);
uint64_t fp_cmplt64 (uint64_t, uint64_t);
uint64_t fp_cmple64 (uint64_t, uint64_t);
uint64_t fp_roundtoint64 (uint32_t, uint64_t);
uint64_t fp_toint64 (uint32_t, uint64_t);
uint64_t fp_fromint64 (uint32_t, uint64_t);
uint64_t fp_fromstring64 (char*);
char* fp_restfromstring64 (char*);

uint64_t fp32_to_fp64 (uint32_t);
fp32 fp64_to_fp32 (uint32_t, uint64_t);
