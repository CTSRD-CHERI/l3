(* -------------------------------------------------------------------------
   32-bit Floating-point
   ------------------------------------------------------------------------- *)

structure FP32 :> FP =
struct

  type ieee_flags = SSE.ieee_flags

  fun dest_fp32 i =
    let
      val w = Word32.fromInt i
    in
      { Sign = Word32.andb (w, 0wx80000000) = 0wx80000000
      , Exponent = Word32.andb (Word32.>> (w, 0w23), 0wxFF)
      , Significand = Word32.andb (w, 0wx7FFFFF)
      }
    end

  fun msb s = Word32.andb (s, 0wx400000) = 0wx400000
  val dst = dest_fp32 o IntInf.toInt o BitsN.toNat
  val toNativeNat = LargeInt.toInt o BitsN.toNat

  fun mk_fp32 {Sign, Exponent, Significand} =
    Word32.toInt
      (Word32.orb
         (Word32.orb
            (if Sign then 0wx80000000 else 0w0, Word32.<< (Exponent, 0w23)),
          Significand))

  fun mk r = BitsN.fromInt (r, 32)
  val mk32 = mk o Word32.toLargeInt

  val negInf  = mk 0xFF800000
  val negMax  = mk 0xFF7FFFFF
  val negMin  = mk 0x80000001
  val negZero = mk 0x80000000

  val posZero = mk 0x00000000
  val posMin  = mk 0x00000001
  val posMax  = mk 0x7F7FFFFF
  val posInf  = mk 0x7F800000

  val qNan = mk 0x7FC00000
  val sNan = mk 0x7F800001

  fun isNan w =
    let val x = dst w in #Exponent x = 0wxff andalso #Significand x <> 0w0 end

  fun isSignallingNan w = isNan w andalso not (msb (#Significand (dst w)))

  fun isFinite w = #Exponent (dst w) <> 0wxff

  fun isNormal w =
    let val {Exponent = e, ...} = dst w in e <> 0wxff andalso e <> 0w0 end

  fun isSubnormal w =
    let val x = dst w in #Exponent x = 0w0 andalso #Significand x <> 0w0 end

  fun isZero w =
    let val x = dst w in #Exponent x = 0w0 andalso #Significand x = 0w0 end

  fun abs w = BitsN.&& (w, mk 0x7FFFFFFF)
  fun neg w = BitsN.?? (w, mk 0x80000000)

  fun mk32' (flags, r) = (flags, mk32 r)

  fun binop
    (f : IEEEReal.rounding_mode * int * int -> 'b * Word32.word)
    (m, (a, b)) =
      mk32' (f (m, toNativeNat a, toNativeNat b))
  fun triop
    (f : IEEEReal.rounding_mode * int * int * int -> 'b * Word32.word)
    (m, (a, (b, c))) =
    mk32' (f (m, toNativeNat a, toNativeNat b, toNativeNat c))
  fun cmpop f (a, b) = f (toNativeNat a, toNativeNat b)

  fun sqrt (m, a) = mk32' (SSE.fp_sqrt32 (m, toNativeNat a))

  val add = binop SSE.fp_add32
  val sub = binop SSE.fp_sub32
  val mul = binop SSE.fp_mul32
  val op div = binop SSE.fp_div32

  val mul_add =
    if SSE.has_fma() then triop SSE.fp_fma32
    else fn _ => raise Fail "Fused multiply add not supported on host machine"

  val mul_sub =
    if SSE.has_fma() then triop SSE.fp_fms32
    else fn _ => raise Fail "Fused multiply sub not supported on host machine"

  fun roundToIntegral (m, a) =
    BitsN.fromNativeInt (SSE.fp_roundtoint32 (m, toNativeNat a), 32)

  fun isIntegral w =
    isFinite w andalso roundToIntegral (IEEEReal.TO_ZERO, w) = w

  val equal = cmpop SSE.fp_cmpeq32
  val lessThan = cmpop SSE.fp_cmplt32
  val lessEqual = cmpop SSE.fp_cmple32

  fun greaterThan (a, b) = lessThan (b, a)
  fun greaterEqual (a, b) = lessEqual (b, a)

  fun compare (a, b) =
    if isNan a orelse isNan b
      then IEEEReal.UNORDERED
    else if equal (a, b)
      then IEEEReal.EQUAL
    else if lessThan (a, b)
      then IEEEReal.LESS
    else IEEEReal.GREATER

  fun fromString s =
    if SSE.fp_restfromstring32 s = "" then
      SOME (mk (IntInf.fromInt (SSE.fp_fromstring32 s)))
    else NONE

  fun fromInt (m, i) =
     if ~0x8000000000000000 <= i andalso i <= 0x7FFFFFFFFFFFFFFF
       then mk (LargeInt.fromInt (SSE.fp_fromint32 (m, i)))
     else raise Fail "FP32.fromInt: too large"

  fun toInt (mode, w) =
    let
      val {Exponent = e, Significand = m, Sign = s} = dst w
    in
      if e = 0wxff
        then NONE
      else if Word32.<= (e, (* bias *) 0w127 + (* precision *) 0w23)
        then SOME (SSE.fp_toint32 (mode, toNativeNat w))
      else let
             val j =
               mk_fp32 {Exponent = 0w127 + 0w23, Significand = m, Sign = s}
           in
             SOME (IntInf.<< (SSE.fp_toint32 (mode, j),
                              Word.fromLargeWord
                                (Word32.toLargeWord (e - (0w127 + 0w23)))))
           end
    end

end (* FP32 *)
