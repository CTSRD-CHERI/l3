(* -------------------------------------------------------------------------
   64-bit Floating-point
   ------------------------------------------------------------------------- *)

structure FP64 :> FP =
struct

  type ieee_flags = SSE.ieee_flags

  fun dest_fp64 i =
    let
      val w = Word64.fromLargeInt i
    in
      { Sign = Word64.andb (w, 0wx8000000000000000) = 0wx8000000000000000
      , Exponent = Word64.andb (Word64.>> (w, 0w52), 0wx7FF)
      , Significand = Word64.andb (w, 0wxFFFFFFFFFFFFF)
      }
    end

  val dst = dest_fp64 o BitsN.toNat
  fun msb s = Word64.andb (s, 0wx8000000000000) = 0wx8000000000000

  fun mk_fp64 {Sign, Exponent, Significand} =
    Word64.toLargeInt
      (Word64.orb
         (Word64.orb
            (if Sign then 0wx8000000000000000 else 0w0,
             Word64.<< (Exponent, 0w52)),
          Significand))

  fun mk r = BitsN.fromInt (r, 64)
  val mk64 = mk o Word64.toLargeInt

  val negInf  = mk 0xFFF0000000000000
  val negMax  = mk 0xFFEFFFFFFFFFFFFF
  val negMin  = mk 0x8000000000000001
  val negZero = mk 0x8000000000000000

  val posZero = mk 0x0000000000000000
  val posMin  = mk 0x0000000000000001
  val posMax  = mk 0x7FEFFFFFFFFFFFFF
  val posInf  = mk 0x7FF0000000000000

  val qNan = mk 0x7FF8000000000000
  val sNan = mk 0x7FF0000000000001

  fun isNan w =
    let val x = dst w in #Exponent x = 0wx7ff andalso #Significand x <> 0w0 end

  fun isSignallingNan w = isNan w andalso not (msb (#Significand (dst w)))

  fun isFinite w = #Exponent (dst w) <> 0wx7ff

  fun isNormal w =
    let val {Exponent = e, ...} = dst w in e <> 0wx7ff andalso e <> 0w0 end

  fun isSubnormal w =
    let val x = dst w in #Exponent x = 0w0 andalso #Significand x <> 0w0 end

  fun isZero w =
    let val x = dst w in #Exponent x = 0w0 andalso #Significand x = 0w0 end

  fun abs w = BitsN.&& (w, mk 0x7FFFFFFFFFFFFFFF)
  fun neg w = BitsN.?? (w, mk 0x8000000000000000)

  fun mk64' (flags, r) = (flags, mk64 r)

  fun binop f (m, (a, b)) = mk64' (f (m, BitsN.toNat a, BitsN.toNat b))
  fun triop f (m, (a, (b, c))) =
    mk64' (f (m, BitsN.toNat a, BitsN.toNat b, BitsN.toNat c))
  fun cmpop f (a, b) = f (BitsN.toNat a, BitsN.toNat b)

  fun sqrt (m, a) = mk64' (SSE.fp_sqrt64 (m, BitsN.toNat a))

  val add = binop SSE.fp_add64
  val sub = binop SSE.fp_sub64
  val mul = binop SSE.fp_mul64
  val op div = binop SSE.fp_div64

  val mul_add =
    if SSE.has_fma() then triop SSE.fp_fma64
    else fn _ => raise Fail "Fused multiply add not supported on host machine"

  val mul_sub =
    if SSE.has_fma() then triop SSE.fp_fms64
    else fn _ => raise Fail "Fused multiply sub not supported on host machine"

  fun roundToIntegral (m, a) = mk (SSE.fp_roundtoint64 (m, BitsN.toNat a))

  fun isIntegral w =
    isFinite w andalso roundToIntegral (IEEEReal.TO_ZERO, w) = w

  val equal = cmpop SSE.fp_cmpeq64
  val lessThan = cmpop SSE.fp_cmplt64
  val lessEqual = cmpop SSE.fp_cmple64

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
    if SSE.fp_restfromstring64 s = "" then
      SOME (mk (SSE.fp_fromstring64 s))
    else NONE

  local
    val _ = Real.precision = 53 orelse raise Fail "Expecting 64-bit Real"
    fun unbyte b = BitsN.fromNat (Word8.toLargeInt b, 8)
    fun toBits r =
      BitsN.concat
        (List.tabulate
          (8,
           fn i => unbyte (Word8Vector.sub (PackRealLittle.toBytes r, 7 - i))))
    fun withMode m f x =
      let
        val m0 = IEEEReal.getRoundingMode ()
      in
         IEEEReal.setRoundingMode m
       ; f x before IEEEReal.setRoundingMode m0
      end
  in
    fun fromInt (m, i) = toBits (withMode m Real.fromLargeInt i)
  end

  fun toInt (mode, w) =
    let
      val {Exponent = e, Significand = m, Sign = s} = dst w
    in
      if e = 0wx7ff
        then NONE
      else if Word64.<= (e, (* bias *) 0w1023 + (* precision *) 0w53)
        then SOME (SSE.fp_toint64 (mode, BitsN.toNat w))
      else let
             val j =
               mk_fp64 {Exponent = 0w1023 + 0w53, Significand = m, Sign = s}
           in
             SOME (IntInf.<< (SSE.fp_toint64 (mode, j),
                              Word.fromLargeWord (e - (0w1023 + 0w53))))
           end
    end

end (* FP64 *)
