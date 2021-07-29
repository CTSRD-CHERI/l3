signature SSE =
sig
  type ieee_flags = {DivideByZero: bool,
                     InvalidOp: bool,
                     Overflow: bool,
                     Precision: bool,
                     Underflow: bool}

  val ieee_flags_DivideByZero_rupd: ieee_flags * bool -> ieee_flags
  val ieee_flags_InvalidOp_rupd: ieee_flags * bool -> ieee_flags
  val ieee_flags_Overflow_rupd: ieee_flags * bool -> ieee_flags
  val ieee_flags_Precision_rupd: ieee_flags * bool -> ieee_flags
  val ieee_flags_Underflow_rupd: ieee_flags * bool -> ieee_flags
  val fp32_to_fp64: int -> LargeInt.int
  val fp64_to_fp32: IEEEReal.rounding_mode * LargeInt.int -> Word32.word
  val fp64_to_fp32_with_flags: IEEEReal.rounding_mode * LargeInt.int ->
                               ieee_flags * Word32.word
  val fp_add32: IEEEReal.rounding_mode * int * int -> ieee_flags * Word32.word
  val fp_add64: IEEEReal.rounding_mode * LargeInt.int * LargeInt.int ->
                ieee_flags * Word64.word
  val fp_cmpeq32: int * int -> bool
  val fp_cmpeq64: LargeInt.int * LargeInt.int -> bool
  val fp_cmple32: int * int -> bool
  val fp_cmple64: LargeInt.int * LargeInt.int -> bool
  val fp_cmplt32: int * int -> bool
  val fp_cmplt64: LargeInt.int * LargeInt.int -> bool
  val fp_div32: IEEEReal.rounding_mode * int * int -> ieee_flags * Word32.word
  val fp_div64: IEEEReal.rounding_mode * LargeInt.int * LargeInt.int ->
                ieee_flags * Word64.word
  val fp_fma32:
     IEEEReal.rounding_mode * int * int * int -> ieee_flags * Word32.word
  val fp_fma64:
     IEEEReal.rounding_mode * LargeInt.int * LargeInt.int * LargeInt.int ->
     ieee_flags * Word64.word
  val fp_fms32:
     IEEEReal.rounding_mode * int * int * int -> ieee_flags * Word32.word
  val fp_fms64:
     IEEEReal.rounding_mode * LargeInt.int * LargeInt.int * LargeInt.int ->
     ieee_flags * Word64.word
  val fp_fromint32: IEEEReal.rounding_mode * LargeInt.int -> int
  val fp_fromint64: IEEEReal.rounding_mode * LargeInt.int -> LargeInt.int
  val fp_fromstring32: string -> int
  val fp_fromstring64: string -> LargeInt.int
  val fp_mul32: IEEEReal.rounding_mode * int * int -> ieee_flags * Word32.word
  val fp_mul64:
     IEEEReal.rounding_mode * LargeInt.int * LargeInt.int ->
     ieee_flags * Word64.word
  val fp_restfromstring32: string -> string
  val fp_restfromstring64: string -> string
  val fp_sqrt32: IEEEReal.rounding_mode * int -> ieee_flags * Word32.word
  val fp_sqrt64:
     IEEEReal.rounding_mode * LargeInt.int -> ieee_flags * Word64.word
  val fp_sub32:
     IEEEReal.rounding_mode * int * int -> ieee_flags * Word32.word
  val fp_sub64:
     IEEEReal.rounding_mode * LargeInt.int * LargeInt.int ->
     ieee_flags * Word64.word
  val fp_toint32: IEEEReal.rounding_mode * int -> LargeInt.int
  val fp_toint64: IEEEReal.rounding_mode * LargeInt.int -> LargeInt.int
  val fp_roundtoint32: IEEEReal.rounding_mode * int -> int
  val fp_roundtoint64: IEEEReal.rounding_mode * LargeInt.int -> LargeInt.int
  val has_fma: unit -> bool
end
