structure FPConvert :> FPConvert =
struct

  fun mk32 r = BitsN.fromInt (Word32.toLargeInt r, 32)
  fun mk64 r = BitsN.fromInt (r, 64)

  val fp32_to_fp64 = mk64 o SSE.fp32_to_fp64 o LargeInt.toInt o BitsN.toUInt
  fun fp64_to_fp32 (m, w) = mk32 (SSE.fp64_to_fp32 (m, BitsN.toUInt w))
  fun fp64_to_fp32_with_flags (m, w) =
    let val (f, r) = SSE.fp64_to_fp32_with_flags (m, BitsN.toUInt w)
    in (f, mk32 r) end

end (* FPConvert *)
