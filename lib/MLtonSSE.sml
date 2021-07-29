(* structure SSE = *)
structure SSE :> SSE =
struct

(* -------------------------------------------------------------------------
   MLton FFI to SSE code in C
   ------------------------------------------------------------------------- *)

val has_fma = _import "has_fma" : unit -> bool;

val fp_add32_result =
  _import "fp_add32_result" :
  Word32.word * Word32.word * Word32.word -> Word32.word;

val fp_add32_mxcsr =
  _import "fp_add32_mxcsr" :
  Word32.word * Word32.word * Word32.word -> Word32.word;

val fp_sub32_result =
  _import "fp_sub32_result" :
  Word32.word * Word32.word * Word32.word -> Word32.word;

val fp_sub32_mxcsr =
  _import "fp_sub32_mxcsr" :
  Word32.word * Word32.word * Word32.word -> Word32.word;

val fp_mul32_result =
  _import "fp_mul32_result" :
  Word32.word * Word32.word * Word32.word -> Word32.word;

val fp_mul32_mxcsr =
  _import "fp_mul32_mxcsr" :
  Word32.word * Word32.word * Word32.word -> Word32.word;

val fp_div32_result =
  _import "fp_div32_result" :
  Word32.word * Word32.word * Word32.word -> Word32.word;

val fp_div32_mxcsr =
  _import "fp_div32_mxcsr" :
  Word32.word * Word32.word * Word32.word -> Word32.word;

val fp_sqrt32_result =
  _import "fp_sqrt32_result" : Word32.word * Word32.word -> Word32.word;

val fp_sqrt32_mxcsr =
  _import "fp_sqrt32_mxcsr" : Word32.word * Word32.word -> Word32.word;

val fp_fma32_result =
  _import "fp_fma32_result" :
  Word32.word * Word32.word * Word32.word * Word32.word -> Word32.word;

val fp_fma32_mxcsr =
  _import "fp_fma32_mxcsr" :
  Word32.word * Word32.word * Word32.word * Word32.word -> Word32.word;

val fp_fms32_result =
  _import "fp_fms32_result" :
  Word32.word * Word32.word * Word32.word * Word32.word -> Word32.word;

val fp_fms32_mxcsr =
  _import "fp_fms32_mxcsr" :
  Word32.word * Word32.word * Word32.word * Word32.word -> Word32.word;

val fp_cmpeq32_ = _import "fp_cmpeq32" : Word32.word * Word32.word -> bool;
val fp_cmplt32_ = _import "fp_cmplt32" : Word32.word * Word32.word -> bool;
val fp_cmple32_ = _import "fp_cmple32" : Word32.word * Word32.word -> bool;

val fp_roundtoint32_ =
  _import "fp_roundtoint32" : Word32.word * Word32.word -> Word32.word;

val fp_toint32_ =
  _import "fp_toint32" : Word32.word * Word32.word -> Word64.word;

val fp_fromint32_ =
  _import "fp_fromint32" : Word32.word * Word64.word -> Word32.word;

val fp_fromstring32_ = _import "fp_fromstring32" : string -> Word32.word;

val fp_restfromstring32 = _import "fp_restfromstring32" : string -> string;

val fp_add64_result =
  _import "fp_add64_result" :
  Word32.word * Word64.word * Word64.word -> Word64.word;

val fp_add64_mxcsr =
  _import "fp_add64_mxcsr" :
  Word32.word * Word64.word * Word64.word -> Word32.word;

val fp_sub64_result =
  _import "fp_sub64_result" :
  Word32.word * Word64.word * Word64.word -> Word64.word;

val fp_sub64_mxcsr =
  _import "fp_sub64_mxcsr" :
  Word32.word * Word64.word * Word64.word -> Word32.word;

val fp_mul64_result =
  _import "fp_mul64_result" :
  Word32.word * Word64.word * Word64.word -> Word64.word;

val fp_mul64_mxcsr =
  _import "fp_mul64_mxcsr" :
  Word32.word * Word64.word * Word64.word -> Word32.word;

val fp_div64_result =
  _import "fp_div64_result" :
  Word32.word * Word64.word * Word64.word -> Word64.word;

val fp_div64_mxcsr =
  _import "fp_div64_mxcsr" :
  Word32.word * Word64.word * Word64.word -> Word32.word;

val fp_sqrt64_result =
  _import "fp_sqrt64_result" : Word32.word * Word64.word -> Word64.word;

val fp_sqrt64_mxcsr =
  _import "fp_sqrt64_mxcsr" : Word32.word * Word64.word -> Word32.word;

val fp_fma64_result =
  _import "fp_fma64_result" :
  Word32.word * Word64.word * Word64.word * Word64.word -> Word64.word;

val fp_fma64_mxcsr =
  _import "fp_fma64_mxcsr" :
  Word32.word * Word64.word * Word64.word * Word64.word -> Word32.word;

val fp_fms64_result =
  _import "fp_fms64_result" :
  Word32.word * Word64.word * Word64.word * Word64.word -> Word64.word;

val fp_fms64_mxcsr =
  _import "fp_fms64_mxcsr" :
  Word32.word * Word64.word * Word64.word * Word64.word -> Word32.word;

val fp_cmpeq64_ = _import "fp_cmpeq64" : Word64.word * Word64.word -> bool;
val fp_cmplt64_ = _import "fp_cmplt64" : Word64.word * Word64.word -> bool;
val fp_cmple64_ = _import "fp_cmple64" : Word64.word * Word64.word -> bool;

val fp_roundtoint64_ =
  _import "fp_roundtoint64" : Word32.word * Word64.word -> Word64.word;

val fp_toint64_ =
  _import "fp_toint64" : Word32.word * Word64.word -> Word64.word;

val fp_fromint64_ =
  _import "fp_fromint64" : Word32.word * Word64.word -> Word64.word;

val fp_fromstring64_ = _import "fp_fromstring64" : string -> Word64.word;

val fp_restfromstring64 = _import "fp_restfromstring64" : string -> string;

val fp32_to_fp64_ = _import "fp32_to_fp64" : Word32.word -> Word64.word;
val fp64_to_fp32_result =
  _import "fp64_to_fp32_result" : Word32.word * Word64.word -> Word32.word;
val fp64_to_fp32_mxcsr =
  _import "fp64_to_fp32_mxcsr" : Word32.word * Word64.word -> Word32.word;

(* ------------------------------------------------------------------------- *)

type ieee_flags = {DivideByZero: bool,
                   InvalidOp: bool,
                   Overflow: bool,
                   Precision: bool,
                   Underflow: bool}

fun decode_mxcsr m =
  { Precision    = Word32.andb (m, 0w32) = 0w32
  , Underflow    = Word32.andb (m, 0w16) = 0w16
  , Overflow     = Word32.andb (m, 0w8) = 0w8
  , DivideByZero = Word32.andb (m, 0w4) = 0w4
(*, DenormalArg  = Word32.andb (m, 0w2) = 0w2 *)
  , InvalidOp    = Word32.andb (m, 0w1) = 0w1
  }

fun ieee_flags_DivideByZero_rupd
  ({DivideByZero, InvalidOp, Overflow = overflow,
    Precision, Underflow} : ieee_flags, b) =
  {DivideByZero = b,
   InvalidOp = InvalidOp,
   Overflow = overflow,
   Precision = Precision,
   Underflow = Underflow} : ieee_flags

fun ieee_flags_InvalidOp_rupd
  ({DivideByZero, InvalidOp, Overflow = overflow,
    Precision, Underflow} : ieee_flags, b) =
  {DivideByZero = DivideByZero,
   InvalidOp = b,
   Overflow = overflow,
   Precision = Precision,
   Underflow = Underflow}

fun ieee_flags_Overflow_rupd
  ({DivideByZero, InvalidOp, Overflow = overflow,
    Precision, Underflow} : ieee_flags, b) =
  {DivideByZero = DivideByZero,
   InvalidOp = InvalidOp,
   Overflow = b,
   Precision = Precision,
   Underflow = Underflow}

fun ieee_flags_Precision_rupd
  ({DivideByZero, InvalidOp, Overflow = overflow,
    Precision, Underflow} : ieee_flags, b) =
  {DivideByZero = DivideByZero,
   InvalidOp = InvalidOp,
   Overflow = overflow,
   Precision = b,
   Underflow = Underflow}

fun ieee_flags_Underflow_rupd
  ({DivideByZero, InvalidOp, Overflow = overflow,
    Precision, Underflow} : ieee_flags, b) =
  {DivideByZero = DivideByZero,
   InvalidOp = InvalidOp,
   Overflow = overflow,
   Precision = Precision,
   Underflow = b}

val rm =
  fn IEEEReal.TO_NEAREST => 0w0 : Word32.word
   | IEEEReal.TO_NEGINF => 0w1
   | IEEEReal.TO_POSINF => 0w2
   | IEEEReal.TO_ZERO => 0w3

fun fp32_monop (f, g) (m, a) =
  let
    val a = (rm m, Word32.fromInt a)
  in
    (decode_mxcsr (f a), g a : Word32.word)
  end

fun fp32_binop (f, g) (m, a, b) =
  let
    val a = (rm m, Word32.fromInt a, Word32.fromInt b)
  in
    (decode_mxcsr (f a), g a : Word32.word)
  end

fun fp32_triop (f, g) (m, a, b, c) =
  let
    val a = (rm m, Word32.fromInt a, Word32.fromInt b, Word32.fromInt c)
  in
    (decode_mxcsr (f a), g a : Word32.word)
  end

fun fp32_cmp f (a, b) = f (Word32.fromInt a, Word32.fromInt b)

fun fp64_monop (f, g) (m, a) =
  let
    val a = (rm m, Word64.fromLargeInt a)
  in
    (decode_mxcsr (f a), g a : Word64.word)
  end

fun fp64_binop (f, g) (m, a, b) =
  let
    val a = (rm m, Word64.fromLargeInt a, Word64.fromLargeInt b)
  in
    (decode_mxcsr (f a), g a : Word64.word)
  end

fun fp64_triop (f, g) (m, a, b, c) =
  let
    val a = (rm m, Word64.fromLargeInt a, Word64.fromLargeInt b,
             Word64.fromLargeInt c)
  in
    (decode_mxcsr (f a), g a : Word64.word)
  end

fun fp64_cmp f (a, b) = f (Word64.fromLargeInt a, Word64.fromLargeInt b)

val fp_add32   = fp32_binop (fp_add32_mxcsr, fp_add32_result)
val fp_sub32   = fp32_binop (fp_sub32_mxcsr, fp_sub32_result)
val fp_mul32   = fp32_binop (fp_mul32_mxcsr, fp_mul32_result)
val fp_div32   = fp32_binop (fp_div32_mxcsr, fp_div32_result)
val fp_sqrt32  = fp32_monop (fp_sqrt32_mxcsr, fp_sqrt32_result)
val fp_fma32   = fp32_triop (fp_fma32_mxcsr, fp_fma32_result)
val fp_fms32   = fp32_triop (fp_fms32_mxcsr, fp_fms32_result)
val fp_cmpeq32 = fp32_cmp fp_cmpeq32_
val fp_cmplt32 = fp32_cmp fp_cmplt32_
val fp_cmple32 = fp32_cmp fp_cmple32_

fun fp_roundtoint32 (m, a) =
  Word32.toInt (fp_roundtoint32_ (rm m, Word32.fromInt a))
fun fp_toint32 (m, a) = Word64.toLargeInt (fp_toint32_ (rm m, Word32.fromInt a))
fun fp_fromint32 (m, a) =
  Word32.toInt (fp_fromint32_ (rm m, Word64.fromLargeInt a))
val fp_fromstring32 = Word32.toInt o fp_fromstring32_

val fp_add64   = fp64_binop (fp_add64_mxcsr, fp_add64_result)
val fp_sub64   = fp64_binop (fp_sub64_mxcsr, fp_sub64_result)
val fp_mul64   = fp64_binop (fp_mul64_mxcsr, fp_mul64_result)
val fp_div64   = fp64_binop (fp_div64_mxcsr, fp_div64_result)
val fp_sqrt64  = fp64_monop (fp_sqrt64_mxcsr, fp_sqrt64_result)
val fp_fma64   = fp64_triop (fp_fma64_mxcsr, fp_fma64_result)
val fp_fms64   = fp64_triop (fp_fms64_mxcsr, fp_fms64_result)
val fp_cmpeq64 = fp64_cmp fp_cmpeq64_
val fp_cmplt64 = fp64_cmp fp_cmplt64_
val fp_cmple64 = fp64_cmp fp_cmple64_

fun fp_roundtoint64 (m, a) =
  Word64.toLargeInt (fp_roundtoint64_ (rm m, Word64.fromLargeInt a))
fun fp_toint64 (m, a) =
  Word64.toLargeInt (fp_toint64_ (rm m, Word64.fromLargeInt a))
fun fp_fromint64 (m, a) =
  Word64.toLargeInt (fp_fromint64_ (rm m, Word64.fromLargeInt a))
val fp_fromstring64 = Word64.toLargeInt o fp_fromstring64_

val fp32_to_fp64 = Word64.toLargeInt o fp32_to_fp64_ o Word32.fromInt
fun fp64_to_fp32 (m, a) = fp64_to_fp32_result (rm m, Word64.fromLargeInt a)
fun fp64_to_fp32_with_flags (m, a) =
  let
    val a = (rm m, Word64.fromLargeInt a)
  in
    (decode_mxcsr (fp64_to_fp32_mxcsr a),  fp64_to_fp32_result a)
  end

end
