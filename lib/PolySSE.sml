structure SSE :> SSE =
struct

open Foreign

type ieee_flags = {DivideByZero: bool,
                   InvalidOp: bool,
                   Overflow: bool,
                   Precision: bool,
                   Underflow: bool}

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

fun decode_mxcsr mxcsr =
  let
    val m = Word32.fromInt mxcsr
  in
    { Precision    = Word32.andb (m, 0w32) = 0w32
    , Underflow    = Word32.andb (m, 0w16) = 0w16
    , Overflow     = Word32.andb (m, 0w8) = 0w8
    , DivideByZero = Word32.andb (m, 0w4) = 0w4
 (* , DenormalArg  = Word32.andb (m, 0w2) = 0w2 *)
    , InvalidOp    = Word32.andb (m, 0w1) = 0w1
    }
  end

fun fp32 (a, b) = (decode_mxcsr a,  Word32.fromInt b)
fun fp64 (a, b) = (decode_mxcsr a, Word64.fromLargeInt b)

val rm =
  fn IEEEReal.TO_NEAREST => 0
   | IEEEReal.TO_NEGINF => 1
   | IEEEReal.TO_POSINF => 2
   | IEEEReal.TO_ZERO => 3

val sse_sym =
  getSymbol
    (loadLibrary
       (OS.Path.joinDirFile {dir = L3.libdir(), file = "sse_float.dynlib"}))

fun fp32_monop s =
  fp32 o
  buildCall2 (sse_sym s, (cUint32, cUint32), cStruct2 (cUint32, cUint32)) o
  (fn (a, b) => (rm a, b))

fun fp32_binop s =
  fp32 o
  buildCall3 (sse_sym s, (cUint32, cUint32, cUint32),
              cStruct2 (cUint32, cUint32)) o
  (fn (a, b, c) => (rm a, b, c))

fun fp32_triop s =
  fp32 o
  buildCall4 (sse_sym s, (cUint32, cUint32, cUint32, cUint32),
              cStruct2 (cUint32, cUint32)) o
  (fn (a, b, c, d) => (rm a, b, c, d))

fun fp32_cmp s =
  (fn r => r <> 0) o buildCall2 (sse_sym s, (cUint32, cUint32), cUint32)

fun fp64_monop s =
  fp64 o
  buildCall2 (sse_sym s, (cUint32, cUint64Large),
              cStruct2 (cUint32, cUint64Large)) o
  (fn (a, b) => (rm a, b))

fun fp64_binop s =
  fp64 o
  buildCall3 (sse_sym s, (cUint32, cUint64Large, cUint64Large),
              cStruct2 (cUint32, cUint64Large)) o
  (fn (a, b, c) => (rm a, b, c))

fun fp64_triop s =
  fp64 o
  buildCall4 (sse_sym s, (cUint32, cUint64Large, cUint64Large, cUint64Large),
              cStruct2 (cUint32, cUint64Large)) o
  (fn (a, b, c, d) => (rm a, b, c, d))

fun fp64_cmp s =
  (fn r => r <> 0) o
  buildCall2 (sse_sym s, (cUint64Large, cUint64Large), cUint64Large)

val has_fma = (fn i => i = 1) o buildCall0 (sse_sym "has_fma", (), cUint32)
(* val get_mxcsr = buildCall0 (sse_sym "get_mxcsr", (), cUint32) *)
val fp_add32   = fp32_binop "fp_add32"
val fp_sub32   = fp32_binop "fp_sub32"
val fp_mul32   = fp32_binop "fp_mul32"
val fp_div32   = fp32_binop "fp_div32"
val fp_sqrt32  = fp32_monop "fp_sqrt32"
val fp_fma32   = fp32_triop "fp_fma32"
val fp_fms32   = fp32_triop "fp_fms32"
val fp_cmpeq32 = fp32_cmp "fp_cmpeq32"
val fp_cmplt32 = fp32_cmp "fp_cmplt32"
val fp_cmple32 = fp32_cmp "fp_cmple32"
val fp_roundtoint32 =
  buildCall2 (sse_sym "fp_roundtoint32", (cUint32, cUint32), cUint32) o
  (fn (a, b) => (rm a, b))
val fp_toint32 =
  buildCall2 (sse_sym "fp_toint32", (cUint32, cUint32), cInt64Large) o
  (fn (a, b) => (rm a, b))
val fp_fromint32 =
  buildCall2 (sse_sym "fp_fromint32", (cUint32, cInt64Large), cUint32) o
  (fn (a, b) => (rm a, b))
val fp_add64   = fp64_binop "fp_add64"
val fp_sub64   = fp64_binop "fp_sub64"
val fp_mul64   = fp64_binop "fp_mul64"
val fp_div64   = fp64_binop "fp_div64"
val fp_sqrt64  = fp64_monop "fp_sqrt64"
val fp_fma64   = fp64_triop "fp_fma64"
val fp_fms64   = fp64_triop "fp_fms64"
val fp_cmpeq64 = fp64_cmp "fp_cmpeq64"
val fp_cmplt64 = fp64_cmp "fp_cmplt64"
val fp_cmple64 = fp64_cmp "fp_cmple64"
val fp_roundtoint64 =
  buildCall2
    (sse_sym "fp_roundtoint64", (cUint32, cUint64Large), cUint64Large) o
  (fn (a, b) => (rm a, b))
val fp_toint64 =
  buildCall2 (sse_sym "fp_toint64", (cUint32, cUint64Large), cInt64Large) o
  (fn (a, b) => (rm a, b))
val fp_fromint64 =
  buildCall2 (sse_sym "fp_fromint64", (cUint32, cInt64Large), cUint64Large) o
  (fn (a, b) => (rm a, b))
val fp32_to_fp64 = buildCall1 (sse_sym "fp32_to_fp64", cUint32, cUint64Large)
val fp64_to_fp32_with_flags =
  fp32 o
  buildCall2 (sse_sym "fp64_to_fp32", (cUint32, cUint64Large),
              cStruct2 (cUint32, cUint32)) o
  (fn (a, b) => (rm a, b))
val fp64_to_fp32 = #2 o fp64_to_fp32_with_flags
val fp_fromstring32 = buildCall1 (sse_sym "fp_fromstring32", cString, cUint32)
val fp_fromstring64 =
  buildCall1 (sse_sym "fp_fromstring64", cString, cUint64Large)
val fp_restfromstring32 =
  buildCall1 (sse_sym "fp_restfromstring32", cString, cString)
val fp_restfromstring64 =
  buildCall1 (sse_sym "fp_restfromstring64", cString, cString)

(*
fun is_x86_64 () =
  let
    val tmp = OS.FileSys.tmpName ()
  in
    if OS.Process.isSuccess (OS.Process.system ("uname -m >> " ^ tmp))
      then let
             val strm = TextIO.openIn tmp
           in
             String.isPrefix "x86_64" (TextIO.inputAll strm)
             before ( TextIO.closeIn strm ; OS.FileSys.remove tmp )
           end
    else false
  end
*)

end
