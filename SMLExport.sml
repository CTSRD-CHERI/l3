(*
use "Export.sml";
*)

(* ------------------------------------------------------------------------
   Export L3 specifications to Standard ML
   ------------------------------------------------------------------------ *)

signature SMLExport =
sig
   val spec: string * string -> unit
   val export: string -> unit
end

structure SMLExport :> SMLExport =
struct

local
   val reserved =
     Stringset.fromList
     ["abstype", "and", "andalso", "as", "case", "datatype", "do", "else",
      "end", "eqtype", "exception", "fn", "fun", "functor", "handle", "if",
      "in", "include", "infix", "infixr", "let", "local", "nonfix", "o",
      "of", "op", "open", "orelse", "raise", "rec", "sharing", "sig",
      "signature", "struct", "structure", "then", "type", "val", "where",
      "with", "withtype", "while"]
   fun rename checkCons s =
      if checkCons andalso Consts.isConstructor s orelse
         Stringset.member (reserved, s)
         then s ^ "'"
      else String.translate (fn #"@" => "''" (* polymorphic AST entries *)
                              | #"#" => "'"  (* exceptions *)
                              | c => String.str c) s
in
   val renameConsReserved = rename true
   val renameReserved = rename false
end

open PP

local
   val annotateIntInf = ref false
   val exportFunctor = ref false
in
   fun isFunctor () = !exportFunctor
   fun annotatedIntInf i =
     if !annotateIntInf
        then "(" ^ IntInf.toString i ^ ": IntInf.int)"
     else IntInf.toString i
   fun annotatedIntInfHex i =
     if !annotateIntInf
        then "(0x" ^ IntExtra.toHexString i ^ ": IntInf.int)"
     else "0x" ^ IntExtra.toHexString i
   val annotatedInt = annotatedIntInf o IntInf.fromInt
   fun process_destination s =
     let
       val l = List.rev (String.fields (fn c => c = #" ") s)
       val m = ref (Stringmap.empty : unit Stringmap.dict)
       fun check s = (m := Stringmap.extend (!m, s, ()); true)
                     handle Stringmap.Extend => false
       fun process1 s =
         let
           val s = L3.lowercase s
           val (b, s) = if String.isPrefix "no" s
                          then (false, String.extract (s, 2, NONE))
                        else (true, s)
         in
           case s of
              "intinf" => (check s andalso (annotateIntInf := b; true))
            | "functor" => (check s andalso  (exportFunctor := b; true))
            | "" => true
            | _ => false
         end
       fun loop [] = raise Fail "process_destination: empty list"
         | loop (l as (h :: t)) = if process1 h then loop t
                                  else String.concatWith " " (List.rev l)
     in
       annotateIntInf := true
     ; exportFunctor := false
     ; OS.Path.splitDirFile (loop l)
     end
end

val ppR = ppS o renameConsReserved

fun mapSizeFn ((dty, _): Type.ty) =
   case dty of
      Type.ConstType "nat" => (~1, "")
    | Type.ConstType "bool" => (2, "IntExtra.fromBool")
    | Type.ConstType "char" => (256, "L3.ord")
    | Type.ConstType s =>
        (case Types.lookupConst s of
            SOME {def = Types.Constructors (Types.Enum d), ...} =>
               (IntInf.fromInt (Stringmap.numItems d), "Cast." ^ s ^ "ToNat")
          | SOME {def = Types.Typedef ty, ...} => mapSizeFn ty
          | _ => (0, ""))
    | Type.BV i => (IntInf.<< (1, Word.fromInt i), "BitsN.toNat")
    | Type.BVV _ => (~2, "BitsN.toNat")
    | _ => (0, "")

val mapSize = fst o mapSizeFn o Types.expand

datatype map_status =
   NoMap
 | SafeMap
 | BadMap
 | CopyMap of PolyML.pretty

local
  val no_map = fn NoMap => true | _ => false
  val safe = fn NoMap => true | SafeMap => true | _ => false
  open Type
in
  fun getMap ((bty, c): Type.ty) =
    let
      fun getM t =
         case t of
             Prod (t1, t2) =>
               (case (getM t1, getM t2) of
                   (NoMap, NoMap) => NoMap
                 | (BadMap, _) => BadMap
                 | (_, BadMap) => BadMap
                 | (CopyMap pp1, CopyMap pp2) =>
                     CopyMap
                       (ppBracket
                          (ppL (2, [ppS "fn (a, b) =>", ppB (1, 0),
                                    ppL (1, [ppS "(", pp1, ppS " a,",
                                             ppB (1, 0), pp2, ppS " b)"])])))
                 | (CopyMap pp, _) =>
                     CopyMap
                       (ppBracket
                         (ppL (2, [ppS "fn (a, b) =>", ppB (1, 0),
                                   ppL (1, [ppS "(", pp, ppS " a,", ppB (1, 0),
                                            ppS "b)"])])))
                 | (_, CopyMap pp) =>
                     CopyMap
                       (ppBracket
                         (ppL (2, [ppS "fn (a, b) =>", ppB (1, 0),
                                   ppL (1, [ppS "(a,", ppB (1, 0), pp,
                                            ppS " b)"])])))
                 | _ => SafeMap)
           | Arrow (t1, t2) =>
               if mapSize (t1, c) = 0
                 then if safe (getM t2) then SafeMap else BadMap
               else if no_map (getM t2)
                 then CopyMap (ppS "Map.copy")
               else BadMap
           | ParamType (OptionTy, t) =>
               (case getM t of
                   CopyMap pp => CopyMap (ppApp ("Option.map", pp))
                 | s => s)
           | ParamType (_, t) =>
               let val s = getM t in if safe s then s else BadMap end
           | ConstType s =>
               (case Types.lookupConst s of
                   SOME {def = Types.Typedef (t, _), ...} => getM t
                 | SOME {def = Types.Constructors (Types.Construct d), ...} =>
                     if Stringmap.all
                          (fn SOME (t, _) => no_map (getM t) | _ => true) d
                       then NoMap
                     else if Stringmap.all
                               (fn SOME (t, _) => safe (getM t) | _ => true) d
                       then SafeMap
                     else BadMap
                 | SOME {def = Types.Record l, ...} =>
                     if List.all (no_map o getM o fst o snd) l
                       then NoMap
                     else if List.all (safe o getM o fst o snd) l
                       then SafeMap
                     else BadMap
                 | _ => NoMap)
           | _ => NoMap
    in
      getM bty
    end
end

local
   open Type
   val param =
      fn ListTy => "list"
       | OptionTy => "option"
       | SetTy => "list"
   fun pp dty =
      case dty of
         VarType s            => ppS ("'" ^ s)
       | ConstType "unit"     => ppS "unit"
       | ConstType "int"      => ppS "IntInf.int"
       | ConstType "nat"      => ppS "Nat.nat"
       | ConstType "bool"     => ppS "bool"
       | ConstType "char"     => ppS "char"
       | ConstType "ieee_compare"  => ppS "IEEEReal.real_order"
       | ConstType "ieee_flags"    => ppS "SSE.ieee_flags"
       | ConstType "ieee_rounding" => ppS "IEEEReal.rounding_mode"
       | ConstType s          => ppS s
       | BV _                 => ppS "BitsN.nbit"
       | BVV _                => ppS "BitsN.nbit"
       | Prod (a, b)  => ppInfix (pp a, " *", pp b)
       | Arrow (a, b) =>
            if mapSize (a, Constrain.empty) = 0
               then ppInfix (pp a, " ->", pp b)
            else ppL (0, [ppBracket (pp b), ppB (1, 0), ppS "Map.map"])
       | ParamType (ListTy, ConstType "char") => ppS "string"
       | ParamType (p, t) =>
            ppL (0, [ppBracket (pp t), ppB (1, 0), ppS (param p)])
in
   fun ppType ty = pp (fst (Types.expand ty))
end

local
    fun ppTypeDecl b (name, p) =
       let
          val (s1, s2) = if b then ("datatype ", "") else ("type ", " =")
       in
          SOME (PolyML.PrettyBlock
                  (0, false, [], [ppS (s1 ^ name ^ s2), ppB (1, 2), p]))
       end
   fun ppRec (n, t) = ppL (1, [ppS (n ^ ":"), ppB (1, 3), ppType t])
   fun ppCons first =
      let
         fun f n = ppS ((if first then "= " else "| ") ^ renameReserved n)
      in
         fn (n, SOME ty) =>
              ppL (4, [f n, ppS " of", ppB (1, 0), ppType ty])
          | (n, NONE) => f n
      end
   fun ppTypeDefArg (name, d) =
      case d of
        Types.Constructors (Types.Enum m) =>
          let
             val l =
                m |> Stringmap.listItems
                  |> msort (Int.compare o (snd ## snd))
                  |> (fn (h, _) :: t =>
                         ppS ("= " ^ h) ::
                         List.concat
                           (List.map
                             (fn (s, _) => [ppB (1, 0), ppS ("| " ^ s)]) t)
                       | [] => raise Fail "ppTypeDefArg: empty")
          in
             ppTypeDecl true (name, PolyML.PrettyBlock (0, false, [], l))
          end
      | Types.Constructors (Types.Construct m) =>
          let
             val l = m |> Stringmap.listItems
                       |> (fn h :: t =>
                               ppCons true h :: List.map (ppCons false) t
                            | [] => raise Fail "ppTypeDefArg: empty")
          in
             ppTypeDecl true (name, ppBL (0, 0, l))
          end
      | Types.Record l =>
          let
             val l = [ppS "{", ppB (1, 1)] @
                     mapSeparate I [ppS ",", ppB (1, 0)] (List.map ppRec l) @
                     [ppB (1, 0), ppS "}"]
          in
             ppTypeDecl false (name, ppL (2, l))
          end
      | _ => NONE
   fun ppTypeDef (name, d: Types.typeconst) = ppTypeDefArg (name, #def d)
in
   fun ppTypeDefs () = List.mapPartial ppTypeDef (Types.listConsts ())
end

(* - printing of enumated type maps and record update functions ----------- *)

local
   fun ppLine c b start x =
      ppS ((if start then "     " else "| ") ^ c x ^ " => " ^ b x)
   fun ppEnum (f, g, c, b, d) (name, []) = raise Fail "ppEnum: empty"
     | ppEnum (f, g, c, b, d) (name, h :: t) =
      PolyML.PrettyBlock (0, true, [],
         [ppS ("fun " ^ f name ^ " x ="), ppB (1, 2),
          ppS ("case " ^ g ^ "x of"), ppB (1, 0),
          PolyML.PrettyBlock (3, true, [],
             mapSeparate I [ppB (1, 0)]
               (ppLine c b true h :: List.map (ppLine c b false) t @
                (if d then [ppS ("| _ => raise Fail \"" ^ f name ^ "\"")]
                 else [])))])
   val ppNatTo =
      ppEnum (fn s => "natTo" ^ s, "Nat.toInt ", annotatedInt o snd, fst, true)
   val ppToNat =
      ppEnum (fn s => s ^ "ToNat", "", fst, annotatedInt o snd, false)
   fun ppToString x =
      ppEnum (fn s => s ^ "ToString", "", fst, quote o fst, false) x
   fun ppStringTo x =
      ppEnum (fn s => "stringTo" ^ s, "", quote o fst, fst, true) x
   val items = Lib.msort (fn ((_, x), (_, y)) => Int.compare (x, y)) o
               Stringmap.listItems
in
   fun ppTypeCasts () =
      let
         val l =
            List.mapPartial
              (fn (name, {def = Types.Constructors (Types.Enum m), ...}) =>
                 SOME (name, items m)
                | _ => NONE) (Types.listConsts ())
      in
         if List.null l
            then []
         else [PolyML.PrettyBlock (0, true, [],
                 [ppS "structure Cast =", ppB (1, 0), ppS "struct",
                  ppB (1, 0)] @
                 mapSeparate I [ppS "\n\n"]
                    (List.map ppNatTo l @ List.map ppToNat l @
                     List.map ppToString l @ List.map ppStringTo l) @
                 [ppB (1, 0), ppS "end"])]
      end
   fun ppTypeCastsSig () =
      let
         val l =
            List.mapPartial
              (fn (name, {def = Types.Constructors (Types.Enum _), ...}) =>
                 SOME name
                | _ => NONE) (Types.listConsts ())
      in
         if List.null l
            then []
         else [PolyML.PrettyBlock (0, true, [],
                 [ppS "structure Cast:", ppB (1, 0), ppS "sig",
                  ppB (1, 0)] @
                 List.concat
                    (List.map (fn s =>
                       [
                        ppS ("\nval natTo" ^ s ^ ": "),
                        ppS ("Nat.nat -> " ^ s),
                        ppS ("\nval " ^ s ^ "ToNat: "),
                        ppS (s ^ " -> Nat.nat"),
                        ppS ("\nval stringTo" ^ s ^ ": "),
                        ppS ("string -> " ^ s),
                        ppS ("\nval " ^ s ^ "ToString: "),
                        ppS (s ^ " -> string")
                       ]) l) @
                 [ppB (1, 0), ppS "\nend\n"])]
      end
end

local
   fun ppUpdate f =
      List.map (fn fld => ppL (2, [ppS fld, ppS " =", ppB (1, 0),
                                   ppS (if f = fld then "x'" else fld)]))
   val ppRec = ppParen ("{", [ppS ",", ppB (1, 0)], "}")
   fun ppRecordUpdateFun (name, l) =
      let
         val p = ppRec (List.map ppS l)
      in
         List.map (fn fld =>
           PolyML.PrettyBlock (2, false, [],
              [ppS ("fun " ^ name ^ "_" ^ fld ^ "_rupd ("), p, ppB (0, 0),
               ppS (": " ^ name ^ ", x') ="),
               ppB (1, 0), ppRec (ppUpdate fld l), ppB (0,0),
               ppS (": " ^ name)])) l
      end
   fun ppRecordUpdateFunSig (name, l) =
      List.map (fn (fld, ty) =>
        PolyML.PrettyBlock (2, false, [],
           [ppS ("val " ^ name ^ "_" ^ fld ^ "_rupd:"), ppB (1, 0),
            PolyML.PrettyBlock (0, false, [],
               [ppS name, ppB (1, 0), ppS "*", ppB (1, 0),
                ppBracket (ppType ty), ppB (1, 0), ppS "->", ppB (1, 0),
                ppS name])])) l
   fun recordUpdateFuns () =
      List.mapPartial
         (fn (name, {def = Types.Record l, ...}) => SOME (name, l)
           | _ => NONE) (Types.listConsts ())
in
   fun ppRecordUpdateFuns () =
      let
         val l = List.map (I ## List.map fst) (recordUpdateFuns ())
      in
         if List.null l then [] else List.concat (List.map ppRecordUpdateFun l)
      end
   fun ppRecordUpdateFunsSig () =
      let
         val l = recordUpdateFuns ()
      in
         if List.null l
            then []
         else List.concat (List.map ppRecordUpdateFunSig l)
      end
end

(* - printing of exceptions -------------------------------------------- *)

local
   fun ppExc (s, oty) =
      case oty of
         NONE => ppBL (0, 2, [ppS "exception", ppS s])
       | SOME ty => ppL (0, [ppS "exception", ppB (1, 2), ppS s, ppS " of",
                             ppB (1, 2), ppType ty])
in
   val ppExceptions = List.map ppExc o Consts.listExceptions
end

(* - printing of L3 expressions and statements ------------------------- *)

val convertEnum =
   fn "roundTiesToEven" => "IEEEReal.TO_NEAREST"
    | "roundTowardNegative" => "IEEEReal.TO_NEGINF"
    | "roundTowardPositive" => "IEEEReal.TO_POSINF"
    | "roundTowardZero" => "IEEEReal.TO_ZERO"
    | "FP_LT" => "IEEEReal.LESS"
    | "FP_EQ" => "IEEEReal.EQUAL"
    | "FP_GT" => "IEEEReal.GREATER"
    | "FP_UN" => "IEEEReal.UNORDERED"
    | s => s

fun ppLiteral ispat =
   fn Term.Bits (BitsN.B (v, sz)) =>
        if sz < 1 then raise Fail "ppLiteral: bits width < 1"
        else ppAppPair ("BitsN.B", ppS (annotatedIntInfHex v),
                        ppS (if ispat then "_" else annotatedIntInf sz))
    | Term.Bitstring s => PolyML.prettyRepresentation (s, 1000000)
    | Term.Bool true => ppS "true"
    | Term.Bool false => ppS "false"
    | Term.Char c => ppS ("#" ^ quote (Char.toString c))
    | Term.Enum (n, s) =>
       (ppS (convertEnum (Option.valOf (Types.revenum s n)))
        handle Option =>
            raise Fail ("ppLiteral: Enum (" ^ Int.toString n ^ ", " ^ s))
    | Term.Int i => ppS (annotatedIntInf i)
    | Term.Nat n => if n < 0 then raise Fail "ppLiteral: negative nat"
                    else ppS (annotatedIntInf n)
    | Term.Other (s, ty) =>
        (case fst (Types.expand ty) of
            Type.BV 32 =>
              (case s of
                  "FP32_NegZero" => ppS ("FP32.negZero")
                | "FP32_PosZero" => ppS ("FP32.posZero")
                | "FP32_NegInf" => ppS ("FP32.negInf")
                | "FP32_PosInf" => ppS ("FP32.posInf")
                | "FP32_NegMin" => ppS ("FP32.negMin")
                | "FP32_PosMin" => ppS ("FP32.posMin")
                | "FP32_NegMax" => ppS ("FP32.negMax")
                | "FP32_PosMax" => ppS ("FP32.posMax")
                | "FP32_qNan" => ppS ("FP32.qNan")
                | "FP32_sNan" => ppS ("FP32.sNan")
                | _ => ppS s)
          | Type.BV 64 =>
              (case s of
                  "FP64_NegZero" => ppS ("FP64.negZero")
                | "FP64_PosZero" => ppS ("FP64.posZero")
                | "FP64_NegInf" => ppS ("FP64.negInf")
                | "FP64_PosInf" => ppS ("FP64.posInf")
                | "FP64_NegMin" => ppS ("FP64.negMin")
                | "FP64_PosMin" => ppS ("FP64.posMin")
                | "FP64_NegMax" => ppS ("FP64.negMax")
                | "FP64_PosMax" => ppS ("FP64.posMax")
                | "FP64_qNan" => ppS ("FP64.qNan")
                | "FP64_sNan" => ppS ("FP64.sNan")
                | _ => ppS s)
          | Type.BVV n =>
               let
                  val v =
                     IntExtra.toHexString
                       (Option.valOf (IntExtra.fromLit (Tag.remove s)))
               in
                  ppAppPair ("BitsN.BV", ppS ("0x" ^ v), ppS n)
               end
          | _ => (case s of
                     "{}" => ppS "[]"
                   | "Nil" => ppS (if Types.equalTy Type.stringTy ty
                                      then "\"\""
                                   else "[]")
                   | "None" => ppS "NONE"
                   | _ => ppS s))
    | Term.String s => ppQ (String.toString s)
    | Term.Unit => ppS "()"

fun lookupOperation s =
   case Consts.lookupConst s of
      Consts.Definition (_, _, ~1) => Consts.Primitive []
    | c as Consts.Constructor _ =>
        if s = "Some" then Consts.Primitive [] else c
    | c => c

val mopChar =
   Stringset.fromList
     ["IsAlpha", "IsAlphaNum", "IsDigit", "IsHexDigit", "IsLower", "IsSpace",
      "IsUpper"]

fun pick (x as (a, b, c)) ty =
   let
      val is = Types.equalTy ty
   in
      Option.valOf
        (if Option.isSome a andalso Type.isWordTy ty
            then a
         else if Option.isSome b andalso is Type.natTy
            then b
         else if Option.isSome c andalso is Type.intTy
            then c
         else raise Fail "pick")
   end

fun pickTy pty (a: string) b ty = if Types.equalTy pty ty then a else b

val bvShift       = pickTy Type.natTy "" "^"
val pickBitstring = pickTy Type.bitstringTy
val pickString    = pickTy Type.stringTy

fun bvSizeString ty =
   case ty of
      (Type.BV i, _) => annotatedInt i
    | (Type.BVV n, _) => n
    | _ => raise Fail "bvSizeString"

val sTy = Type.sndTy o Types.expand

fun ppMop (f, ty, tty) =
   case f of
      "-"          => pick (SOME "BitsN.neg", NONE, SOME "IntInf.~") ty
    | "~"          => "BitsN.~"
    | "Abs"        => pick (SOME "BitsN.abs", NONE, SOME "IntInf.abs") ty
    | "Concat"     => pickString "String.concat" "List.concat" tty
    | "PadLeft"    => pickString "L3.padLeftString" "L3.padLeft" tty
    | "PadRight"   => pickString "L3.padRightString" "L3.padRight" tty
    | "FP32_Abs"          => "FP32.abs"
    | "FP32_Add"          => "(L3.snd o FP32.add)"
    | "FP32_Add_"         => "FP32.add"
    | "FP32_Compare"      => "FP32.compare"
    | "FP32_Div"          => "(L3.snd o FP32.div)"
    | "FP32_Div_"         => "FP32.div"
    | "FP32_Equal"        => "FP32.equal"
    | "FP32_FromInt"      => "FP32.fromInt"
    | "FP32_GreaterEqual" => "FP32.greaterEqual"
    | "FP32_GreaterThan"  => "FP32.greaterThan"
    | "FP32_IsIntegral"   => "FP32.isIntegral"
    | "FP32_IsFinite"     => "FP32.isFinite"
    | "FP32_IsNan"        => "FP32.isNan"
    | "FP32_IsNormal"     => "FP32.isNormal"
    | "FP32_IsSignallingNan" => "FP32.isSignallingNan"
    | "FP32_IsSubnormal"  => "FP32.isSubnormal"
    | "FP32_IsZero"       => "FP32.isZero"
    | "FP32_LessEqual"    => "FP32.lessEqual"
    | "FP32_LessThan"     => "FP32.lessThan"
    | "FP32_Mul"          => "(L3.snd o FP32.mul)"
    | "FP32_Mul_"         => "FP32.mul"
    | "FP32_MulAdd"       => "(L3.snd o FP32.mul_add)"
    | "FP32_MulAdd_"      => "FP32.mul_add"
    | "FP32_MulSub"       => "(L3.snd o FP32.mul_sub)"
    | "FP32_MulSub_"      => "FP32.mul_sub"
    | "FP32_Neg"          => "FP32.neg"
    | "FP32_RoundToIntegral" => "FP32.roundToIntegral"
    | "FP32_Sqrt"         => "(L3.snd o FP32.sqrt)"
    | "FP32_Sqrt_"        => "FP32.sqrt"
    | "FP32_Sub"          => "(L3.snd o FP32.sub)"
    | "FP32_Sub_"         => "FP32.sub"
    | "FP32_ToInt"        => "FP32.toInt"
    | "FP64_Abs"          => "FP64.abs"
    | "FP64_Add"          => "(L3.snd o FP64.add)"
    | "FP64_Add_"         => "FP64.add"
    | "FP64_Compare"      => "FP64.compare"
    | "FP64_Div"          => "(L3.snd o FP64.div)"
    | "FP64_Div_"         => "FP64.div"
    | "FP64_Equal"        => "FP64.equal"
    | "FP64_FromInt"      => "FP64.fromInt"
    | "FP64_GreaterEqual" => "FP64.greaterEqual"
    | "FP64_GreaterThan"  => "FP64.greaterThan"
    | "FP64_IsIntegral"   => "FP64.isIntegral"
    | "FP64_IsFinite"     => "FP64.isFinite"
    | "FP64_IsNan"        => "FP64.isNan"
    | "FP64_IsNormal"     => "FP64.isNormal"
    | "FP64_IsSignallingNan" => "FP64.isSignallingNan"
    | "FP64_IsSubnormal"  => "FP64.isSubnormal"
    | "FP64_IsZero"       => "FP64.isZero"
    | "FP64_LessEqual"    => "FP64.lessEqual"
    | "FP64_LessThan"     => "FP64.lessThan"
    | "FP64_Mul"          => "(L3.snd o FP64.mul)"
    | "FP64_Mul_"         => "FP64.mul"
    | "FP64_MulAdd"       => "(L3.snd o FP64.mul_add)"
    | "FP64_MulAdd_"      => "FP64.mul_add"
    | "FP64_MulSub"       => "(L3.snd o FP64.mul_sub)"
    | "FP64_MulSub_"      => "FP64.mul_sub"
    | "FP64_Neg"          => "FP64.neg"
    | "FP64_RoundToIntegral" => "FP64.roundToIntegral"
    | "FP64_Sqrt"         => "(L3.snd o FP64.sqrt)"
    | "FP64_Sqrt_"        => "FP64.sqrt"
    | "FP64_Sub"          => "(L3.snd o FP64.sub)"
    | "FP64_Sub_"         => "FP64.sub"
    | "FP64_ToInt"        => "FP64.toInt"
    | "FP32_ToFP64"       => "FPConvert.fp32_to_fp64"
    | "FP64_ToFP32"       => "FPConvert.fp64_to_fp32"
    | "FP64_ToFP32_"      => "FPConvert.fp64_to_fp32_with_flags"
    | "Fst" => "L3.fst"
    | "FromBinString" => "Nat.fromBinString"
    | "FromDecString" => "Nat.fromString"
    | "FromHexString" => "Nat.fromHexString"
    | "Head"       => pickString "L3.strHd" "List.hd" ty
    | "IsSome"     => "Option.isSome"
    | "Length"     => pickString "L3.size" "L3.length" ty
    | "Log2"       => pick (SOME "BitsN.log2", SOME "Nat.log2", NONE) ty
    | "Max"        => pick (SOME "BitsN.max", SOME "Nat.max", SOME "IntInf.max")
                           (Type.fstTy ty)
    | "Min"        => pick (SOME "BitsN.min", SOME "Nat.min", SOME "IntInf.min")
                           (Type.fstTy ty)
    | "Msb"        => "BitsN.msb"
    | "QuotRem"    => "IntInf.quotRem"
    | "Reverse"    => if Type.isWordTy ty then "BitsN.reverse"
                      else pickString "L3.revString" "List.rev" ty
    | "RemoveDuplicates" => pickString "L3.removeDuplicatesString" "Set.mk" tty
    | "SetOfList"  => "Set.mk"
    | "SignExtend" => "BitsN.signExtend " ^ bvSizeString tty
    | "SignedMax"  => "BitsN.smax"
    | "SignedMin"  => "BitsN.smin"
    | "Size"       => "BitsN.size"
    | "Snd"        => "L3.snd"
    | "Some"       => "Option.SOME"
    | "Tail"       => pickString "L3.strTl" "List.tl" ty
    | "ToLower"    => "L3.lowercase"
    | "ToUpper"    => "L3.uppercase"
    | "ValOf"      => "Option.valOf"
    | "ZeroExtend" => "BitsN.zeroExtend " ^ bvSizeString tty
    | "not"        => "not"
    | "Difference" => "Set.diff"
    | "Union"      => "Set.union"
    | "Intersect"  => "Set.intersect"
    | "IsSubset"   => "Set.isSubset"
    | "IsMember"   => pickString "L3.memString" "Set.mem" (sTy ty)
    | "Cardinality"=> "L3.length"
    | "RemoveExcept" => pickString "L3.removeExceptString" "Set.intersect" tty
    | "Take"       => pickString "L3.takeString" "L3.take" tty
    | "Drop"       => pickString "L3.dropString" "L3.drop" tty
    | "Update"     => pickString "L3.stringUpdate" "L3.listUpdate" tty
    | "Remove"     => pickString "L3.removeString" "L3.remove" tty
    | "Element"    => pickString "(String.sub o L3.swap)" "L3.element" (sTy ty)
    | "IndexOf"    => pickString "L3.indexOfString" "L3.indexOf" (sTy ty)
    | _ => if Stringset.member (mopChar, f)
              then "Char.i" ^ String.extract (f, 1, NONE)
           else raise Fail ("ppMop: " ^ f)

fun ppBop (f, ty1, ty2) =
   case f of
      ">>"   => "BitsN.>>" ^ bvShift ty2
    | "#<<"  => "BitsN.#<<" ^ bvShift ty2
    | "#>>"  => pickBitstring "Bitstring.#>>" ("BitsN.#>>" ^ bvShift ty2) ty1
    | ">>+"  => pickBitstring "Bitstring.>>+" ("BitsN.>>+" ^ bvShift ty2) ty1
    | "<<"   => pickBitstring "Bitstring.<<" ("BitsN.<<" ^ bvShift ty2) ty1
    | "&&"   => pickBitstring "Bitstring.&&" "BitsN.&&" ty1
    | "||"   => pickBitstring "Bitstring.||" "BitsN.||" ty1
    | "??"   => pickBitstring "Bitstring.??" "BitsN.??" ty1
    | "+"    => if Types.equalTy Type.bitstringTy ty1
                   then "Bitstring.+"
                else pick (SOME "BitsN.+", SOME "Nat.+", SOME "IntInf.+") ty1
    | "-"    => pick (SOME "BitsN.-", SOME "Nat.-", SOME "IntInf.-") ty1
    | "*"    => pick (SOME "BitsN.*", SOME "Nat.*", SOME "IntInf.*") ty1
    | "**"   => pick (NONE, SOME "Nat.pow", SOME "IntExtra.pow") ty1
    | "<+"   => "BitsN.<+"
    | "<=+"  => "BitsN.<=+"
    | ">+"   => "BitsN.>+"
    | ">=+"  => "BitsN.>=+"
    | "<"    => pick (SOME "BitsN.<", SOME "Nat.<", SOME "IntInf.<") ty1
    | "<="   => pick (SOME "BitsN.<=", SOME "Nat.<=", SOME "IntInf.<=") ty1
    | ">"    => pick (SOME "BitsN.>", SOME "Nat.>", SOME "IntInf.>") ty1
    | ">="   => pick (SOME "BitsN.>=", SOME "Nat.>=", SOME "IntInf.>=") ty1
    | "<.>"  => pickBitstring "Bitstring.bit" "BitsN.bit" ty1
    | "in"     => "Set.mem"
    | "insert" => "Set.insert"
    | "div"  => pick (SOME "BitsN.div", SOME "Nat.div", SOME "IntInf.div") ty1
    | "mod"  => pick (SOME "BitsN.mod", SOME "Nat.mod", SOME "IntInf.mod") ty1
    | "quot" => pick (SOME "BitsN.quot", NONE, SOME "IntInf.quot") ty1
    | "rem"  => pick (SOME "BitsN.rem", NONE, SOME "IntInf.rem") ty1
    | "sdiv" => "BitsN.sdiv"
    | "smod" => "BitsN.smod"
    | "splitl" => "L3.splitl"
    | "splitr" => "L3.splitr"
    | "fields" => "L3.uncurry String.fields"
    | "tokens" => "L3.uncurry String.tokens"
    | f => raise Fail ("ppBop: " ^ f)

val listOfList =
   let
      fun iter a =
         fn tm as Term.Comb ("Cons", _, [t]) =>
              (case Lib.total Term.destPair t of
                  SOME (l, r) => iter (l::a) r
                | NONE => (a, SOME tm))
          | Term.Lit (Term.Other ("Nil", _)) => (a, NONE)
          | tm => (a, SOME tm)
   in
      (List.rev ## I) o iter []
   end

fun stringOfList [] = NONE
  | stringOfList l = SOME (String.implode (List.map Term.destCharLit l))
                     handle Fail _ => NONE

fun mkNatFromInt i = Int.toString i

datatype cast =
     Cast0
   | Cast1 of string
   | Cast2 of string * string
   | Cast3 of string * string * string

fun pickCast (ty1, ty2) =
   case (Types.dest ty1, Types.dest ty2) of
      (Type.Other "bool", Type.Other "bool") => Cast0
    | (Type.Other "char", Type.Other "char") => Cast0
    | (Type.Other "nat",  Type.Other "nat") => Cast0
    | (Type.Other "int",  Type.Other "int") => Cast0
    | (Type.Other "string", Type.Other "string") => Cast0
    | (Type.Other "bitstring", Type.Other "bitstring") => Cast0
    | (Type.Other "bool", Type.Other "char") =>
         Cast1 "(fn true => #\"t\" | false => #\"f\")"
    | (Type.Other "bool", Type.Other "string") =>
         Cast1 "(fn true => \"true\" | false => \"false\")"
    | (Type.Other "bool", Type.Other "nat") => Cast1 "Nat.fromBool"
    | (Type.Other "bool", Type.Other "int") => Cast1 "IntExtra.fromBool"
    | (Type.Other "bool", Type.Other "bitstring") => Cast1 "Bitstring.fromBool"
    | (Type.Other "bool", Type.FixedBits 1) => Cast1 "BitsN.fromBit"
    | (Type.Other "bool", Type.FixedBits i) =>
         Cast1 ("BitsN.fromBool " ^ mkNatFromInt i)
    | (Type.Other "bool", Type.VarBits (N, _)) => Cast1 ("BitsN.fromBool " ^ N)
    | (Type.Other "nat", Type.Other "bool") => Cast1 "(not o L3.equal Nat.zero)"
    | (Type.Other "nat", Type.Other "char") => Cast1 "L3.chr"
    | (Type.Other "nat", Type.Other "string") => Cast1 "Nat.toString"
    | (Type.Other "nat", Type.Other "int") => Cast1 "Nat.toInt"
    | (Type.Other "nat", Type.Other "bitstring") => Cast1 "Bitstring.fromNat"
    | (Type.Other "nat", Type.Other s) =>
         if Types.isEnumerated s
            then Cast1 ("Cast.natTo" ^ s)
         else raise Fail ("nat -> " ^ s)
    | (Type.Other "nat", Type.FixedBits i) =>
         Cast2 ("BitsN.fromNat", mkNatFromInt i)
    | (Type.Other "nat", Type.VarBits (N, _)) => Cast2 ("BitsN.fromNat", N)
    | (Type.Other "int", Type.Other "bool") => Cast1 "(not o L3.equal 0)"
    | (Type.Other "int", Type.Other "char") => Cast1 "L3.chr"
    | (Type.Other "int", Type.Other "string") => Cast1 "IntInf.toString"
    | (Type.Other "int", Type.Other "nat") => Cast1 "Nat.fromInt"
    | (Type.Other "int", Type.Other "bitstring") => Cast1 "Bitstring.fromInt"
    | (Type.Other "int", Type.Other s) =>
         if Types.isEnumerated s
            then Cast1 ("Cast.natTo" ^ s)
         else raise Fail ("int -> " ^ s)
    | (Type.Other "int", Type.FixedBits i) =>
         Cast2 ("BitsN.fromInt", mkNatFromInt i)
    | (Type.Other "int", Type.VarBits (N, _)) => Cast2 ("BitsN.fromInt", N)
    | (Type.Other "bitstring", Type.Other "bool") =>
         Cast1 "(not o L3.equal 0 o Bitstring.toInt)"
    | (Type.Other "bitstring", Type.Other "char") =>
         Cast1 "(L3.chr o Bitstring.toNat)"
    | (Type.Other "bitstring", Type.Other "string") =>
         Cast1 "Bitstring.toBinString"
    | (Type.Other "bitstring", Type.Other "nat") => Cast1 "Bitstring.toNat"
    | (Type.Other "bitstring", Type.Other "int") => Cast1 "Bitstring.toInt"
    | (Type.Other "bitstring", Type.Other s) =>
         if Types.isEnumerated s
            then Cast1 ("(Cast.natTo" ^ s ^ " o Bitstring.toNat)")
         else raise Fail ("bitstring -> " ^ s)
    | (Type.Other "bitstring", Type.FixedBits i) =>
         Cast2 ("BitsN.fromBitstring", mkNatFromInt i)
    | (Type.Other "bitstring", Type.VarBits (N, _)) =>
         Cast2 ("BitsN.fromBitstring", N)
    | (Type.Other "char", Type.Other "bool") => Cast1 "L3.equal #\"t\""
    | (Type.Other "char", Type.Other "string") => Cast1 "String.str"
    | (Type.Other "char", Type.Other "nat") => Cast1 "L3.ord"
    | (Type.Other "char", Type.Other "int") => Cast1 "L3.ord"
    | (Type.Other "char", Type.Other "bitstring") =>
         Cast1 "(Bitstring.fromNat o L3.ord)"
    | (Type.Other "char", Type.Other s) =>
         if Types.isEnumerated s
            then Cast1 ("(Cast.natTo" ^ s ^ " o L3.ord)")
         else raise Fail ("nat -> " ^ s)
    | (Type.Other "char", Type.FixedBits i) =>
         Cast3 ("BitsN.fromNat", "L3.ord", mkNatFromInt i)
    | (Type.Other "char", Type.VarBits (N, _)) =>
         Cast3 ("BitsN.fromNat", "L3.ord", N)
    | (Type.Other "string", Type.Other "bool") =>
         Cast1 "(fn \"true\" => true | \"false\" => false | _ => raise Domain)"
    | (Type.Other "string", Type.Other "char") => Cast1 "L3.stringToChar"
    | (Type.Other "string", Type.Other "int") => Cast1 "IntExtra.fromString"
    | (Type.Other "string", Type.Other "nat") => Cast1 "Nat.fromString"
    | (Type.Other "string", Type.Other "bitstring") =>
         Cast1 "Bitstring.fromBinString"
    | (Type.Other "string", Type.Other s) =>
         if Types.isEnumerated s
            then Cast1 ("Cast.stringTo" ^ s)
         else raise Fail ("string -> " ^ s)
    | (Type.Other "string", Type.FixedBits i) =>
         Cast2 ("(Option.valOf o BitsN.fromHexString)", mkNatFromInt i)
    | (Type.Other "string", Type.VarBits (N, _)) =>
         Cast2 ("(Option.valOf o BitsN.fromHexString)", N)
    | (Type.Other s, Type.Other "char") =>
         if Types.isEnumerated s
            then Cast1 ("(L3.chr o Cast." ^ s ^ "ToNat)")
         else raise Fail (s ^ " -> nat")
    | (Type.Other s, Type.Other s2) =>
         if Types.isEnumerated s
            then case s2 of
                    "string" => Cast1 ("Cast." ^ s ^ "ToString")
                  | "nat"    => Cast1 ("Cast." ^ s ^ "ToNat")
                  | "int"    => Cast1 ("Cast." ^ s ^ "ToNat")
                  | "bitstring" =>
                      Cast1 ("(Bitstring.fromNat o Cast." ^ s ^ "ToNat)")
                  | _ => if s = s2
                            then Cast0
                         else if Types.isEnumerated s2
                            then Cast1 ("(Cast.natTo" ^ s2 ^ " o " ^ "Cast." ^
                                        s ^ "ToNat)")
                         else raise Fail (s ^ " -> " ^ s2)
         else raise Fail (s ^ " -> " ^ s2)
    | (Type.Other s, Type.FixedBits i) =>
         if Types.isEnumerated s
            then Cast3 ("BitsN.fromNat", "Cast." ^ s ^ "ToNat", mkNatFromInt i)
         else raise Fail (s ^ " -> bits(" ^ Int.toString i ^ ")")
    | (Type.Other s, Type.VarBits (N, _)) =>
         if Types.isEnumerated s
            then Cast3 ("BitsN.fromNat", "Cast." ^ s ^ "ToNat", N)
         else raise Fail (s ^ " -> bits(" ^ N ^ ")")
    | (Type.FixedBits i, Type.Other "bool") =>
         Cast1 ("(not o L3.equal (BitsN.zero (" ^ mkNatFromInt i ^ ")))")
    | (Type.FixedBits _, Type.Other "char") => Cast1 "(L3.chr o BitsN.toNat)"
    | (Type.FixedBits _, Type.Other "string") => Cast1 "BitsN.toHexString"
    | (Type.FixedBits _, Type.Other "nat") => Cast1 "BitsN.toNat"
    | (Type.FixedBits _, Type.Other "int") => Cast1 "BitsN.toInt"
    | (Type.FixedBits _, Type.Other "bitstring") => Cast1 "BitsN.toBitstring"
    | (Type.FixedBits i, Type.Other s) =>
         if Types.isEnumerated s
            then Cast1 ("(Cast.natTo" ^ s ^ " o BitsN.toNat)")
         else raise Fail (" `" ^ Int.toString i ^ " -> " ^ s)
    | (Type.FixedBits i, Type.FixedBits j) =>
         if i = j then Cast0
         else Cast3 ("BitsN.fromNat", "BitsN.toNat", mkNatFromInt j)
    | (Type.FixedBits _, Type.VarBits (N, _)) =>
         Cast3 ("BitsN.fromNat", "BitsN.toNat", N)
    | (Type.VarBits (N, _), Type.Other "bool") =>
         Cast1 ("(not o L3.equal (BitsN.zero (" ^ N ^ ")))")
    | (Type.VarBits _, Type.Other "char") => Cast1 "(L3.chr o BitsN.toNat)"
    | (Type.VarBits _, Type.Other "string") => Cast1 "BitsN.toHexString"
    | (Type.VarBits _, Type.Other "nat") => Cast1 "BitsN.toNat"
    | (Type.VarBits _, Type.Other "int") => Cast1 "BitsN.toInt"
    | (Type.VarBits _, Type.Other "bitstring") => Cast1 "BitsN.toBitstring"
    | (Type.VarBits (N, _), Type.Other s) =>
         if Types.isEnumerated s
            then Cast1 ("(Cast.natTo" ^ s ^ " o BitsN.toNat)")
         else raise Fail (" `" ^ N ^ " -> " ^ s)
    | (Type.VarBits _, Type.FixedBits j) =>
         Cast3 ("BitsN.fromNat", "BitsN.toNat", mkNatFromInt j)
    | (Type.VarBits (M, _), Type.VarBits (N, _)) =>
         if M = N then Cast0 else Cast3 ("BitsN.fromNat", "BitsN.toNat", N)
    (*
    | (t1, t2) =>
        ( pp (PolyML.prettyRepresentation (t1, 10))
        ; print "to "
        ; pp (PolyML.prettyRepresentation (t2, 10))
        ; raise Fail ("pickCast: Bad cast")
        )
    *)

fun ppVar (s, ty) =
   ppS (if Types.equalTy Type.unitTy ty then "()" else renameConsReserved s)

val isCond = fn Term.Comb ("i-t-e", _, [_, _, _]) => true
              | _ => false

val isMatch = fn Term.Comb ("match", _, _ :: _) => true
               | _ => false

local
   val destSeq =
      fn Term.Comb (";", _, [a, b]) => (a, b)
       | _ => raise Fail "destSeq"
in
   val destSequence =
      let
         fun iter a t =
            case Lib.total destSeq t of
               SOME (b, c) => iter (b :: a) c
             | NONE => List.rev (t :: a)
      in
         iter []
      end
end

val boolify = ref ([] : string list)
val safemap = ref true

fun expandASTName f = if Tag.isAST f then "dfn'" ^ Tag.remove f else f

fun reference a = String.extract (a, 2, SOME (String.size a - 3))

val bitsTypeVars = Stringset.listItems o Type.freeBitsTypeVars o Term.typeOf

fun noBitsTypeVars f =
  case lookupOperation f of
     Consts.Definition (d, _, _) => List.null (bitsTypeVars d)
   | _ => false

local
  fun mk_suc t = Term.Comb ("+", Type.natTy, [t, Term.mkNatLit 1])
in
  fun bits_width (a, b) =
    case a of
       Term.Comb ("+", _, [x, y]) =>
         Eval.evalNatTerm
           (if Term.equalTm x b
               then mk_suc y
            else if Term.equalTm y b
               then mk_suc x
            else Term.Comb ("-", Type.natTy, [mk_suc a, b]))
     | _ => Eval.evalNatTerm (Term.Comb ("-", Type.natTy, [mk_suc a, b]))
end

fun maybeTuple l =
   case l of
      [] => []
    | [n] => [ppS n]
    | _ => [ppL (2, [ppTuple (List.map ppS l)])]

val impure = ref Stringset.empty

local
   fun getTypeInst m v =
      let
         val l =
            List.mapPartial
               (fn Type.SubstBits (q, x) =>
                     if q = v
                        then case x of
                                Type.FixedBits i => SOME (Int.toString i)
                              | Type.VarBits (s, _) => SOME s
                              | _ => NONE
                     else NONE
                 | _ => NONE) m
      in
         case l of
            [] => v
          | [r] => r
          | x => (printn (PolyML.makestring x); raise Fail "getTypeInst")
      end
in
   fun ppDefn name d a ty =
      let
         val s = renameReserved name
         val vs = bitsTypeVars d
      in
         if List.null vs
            then if List.null a
                   then if Stringset.member (!impure, expandASTName name)
                          then ppApp (s, ppS "()")
                        else ppS s
                 else ppApp (s, hd a)
         else let
                 val tyd = Term.primTypeOf d
                 val m = Types.match tyd ty
                         handle Types.TypeMatch _ =>
                            Types.match (Type.unitTy --> tyd) ty
                 val i = getTypeInst m
                 val x = maybeTuple (List.map i vs)
              in
                 ppL (2, [ppS s, ppB (1, 0)] @ x @
                         (if List.null a then [] else [ppB (1, 0)]) @ a)
              end
      end
end

fun ppExpression t =
   case t of
     Term.Lit (Term.Other ("UNKNOWN", ty)) => ppExpression (Term.genUnknown ty)
   | Term.Lit v => ppLiteral false v
   | Term.Abs ([("_", ty)], _, d) => ppInitMap ty d
   | Term.Abs _ =>
       let
          val (v, b) = Term.destAbs t
       in
          ppL (2, [ppS "fn ", ppExpression v, ppS " =>", ppB (1, 0),
                              ppExpression b])
       end
   | Term.Var s_ty => ppVar s_ty
   | Term.Comb ("abs-apply", _, [Term.Abs ([_], _, _), _]) =>
       let
          val (l, b) = Term.destLets t
          val l =
             List.map (fn (v, e) =>
                ppL (2, [ppS "val ", ppExpression v, ppS " =", ppB (1, 0),
                         ppMapExpression e])) l
             |> mapSeparate I [ppB (1, 2)]
       in
          PolyML.PrettyBlock (0, true, [],
              [ppS "let",
               ppB (1, 2)] @ l @
              [ppB (1, 0),
               ppS "in",
               ppB (1, 2),
               ppExpression b,
               ppB (1, 0),
               ppS "end"])
       end
   | Term.Comb ("abs-apply", _, [f, x]) =>
       let
          val (sz, cst) = mapSizeFn (Types.domain (Term.typeOf f))
          val fe = ppExpression f
          val xe = ppExpression x
       in
          if sz = 0
             then ppL (2, [ppBracket fe, ppB (1, 0), ppBracket xe])
          else ppAppPair ("Map.lookup", fe,
                          if cst = "" then xe else ppApp (cst, xe))
       end
   | Term.Comb ("i-t-e", _, [a, b, c]) =>
       PolyML.PrettyBlock
           (0, true, [],
            [ppS "if ", ppL (3, [ppExpression a]), ppB (1, 2),
             ppS "then ", ppL (7, [ppExpression b]), ppB (1, 0),
             ppS "else "] @
            (if isCond c then [ppExpression c]
             else [ppL (5, [ppExpression c])]))
   | Term.Comb ("update-map", _, [m, i, e]) =>
       let
          val (sz, cst) = mapSizeFn (Types.domain (Term.typeOf m))
          val me = ppExpression m
          val ie = ppExpression i
          val ee = ppMapExpression e
       in
          if sz = 0
             then ppL (0, [ppS "L3.update", ppB (1, 2), ppBracket me,
                           ppB (1, 2), ppBracket ie, ppB (1, 2),
                           ppBracket ee])
          else ppAppTriple ("Map.update", me,
                            if cst = "" then ie else ppApp (cst, ie), ee)
       end
   | Term.Comb ("<..>", ty, [a, b, c]) =>
       let
          val ea = ppExpression a
          val eb = ppExpression b
          val ec = ppBracket (ppExpression c)
          fun pp s = ppBL (0, 2, [ppAppPair (s, ea, eb), ec])
       in
          case Types.dest ty of
             Type.Other "bitstring" => pp "Bitstring.bits"
           | Type.VarBits (N, _) =>
                ppL (2, [ppS "BitsN.resize", ppB (1, 0), ppS N, ppB (1, 0),
                         ppBracket (pp "BitsN.bits")])
           | Type.FixedBits i =>
                if bits_width (a, b) = SOME i
                  then pp "BitsN.bits"
                else ppL (2, [ppS "BitsN.resize", ppB (1, 0),
                              ppS (Int.toString i), ppB (1, 0),
                              ppBracket (pp "BitsN.bits")])
           | _ => raise Fail ("ppExpression: extract has bad return type")
       end
   | Term.Comb ("bit-field-insert", ty, [h, l, a, b]) =>
      ppBL (0, 2,
            [ppAppPair
               (if Types.equalTy Type.bitstringTy ty
                   then "Bitstring.bitFieldInsert"
                else "BitsN.bitFieldInsert", ppExpression h, ppExpression l),
             ppPair (ppExpression a, ppExpression b)])
   | Term.Comb ("{..}", _, l) => ppList (List.map ppExpression l)
   | Term.Comb ("[..]", ty, [a]) =>
       (case pickCast (Term.primTypeOf a, ty) of
           Cast0 => ppExpression a
         | Cast1 f => ppApp (f, ppExpression a)
         | Cast2 (f, b) => ppAppPair (f, ppExpression a, ppS b)
         | Cast3 (f1, f2, b) =>
             ppAppPair (f1, ppApp (f2, ppExpression a), ppS b))
   | Term.Comb ("match", ty, m::l) =>
       ppMatch (m, l)
   | Term.Comb (f, ty, []) =>
        let
           val name = expandASTName f
        in
           case Consts.lookupConst f of
             Consts.Accessor (d, _, _) => ppDefn name d [] ty
           | Consts.Definition (d, _, _) => ppDefn name d [] ty
           | Consts.Exception NONE =>
               ppL (0, [ppS "raise ", ppS (Tag.remove f)])
           | _ => raise Fail ("ppExpression, 0-arg: " ^ f)
        end
   | Term.Comb ("&", ty, [a]) =>
        let
           val n = case Types.dest ty of
                     Type.Other s => "write'reg'" ^ s
                   | Type.FixedBits _ =>
                       (case Term.dTypeOf a of
                          Type.Other s => "reg'" ^ s
                        | _ => raise Fail "ppExpression: bad type for &")
                   | _ => raise Fail "ppExpression: bad type for &"
        in
           ppApp (n, ppExpression a)
        end
   | Term.Comb ("Cons", ty, [a]) =>
        let
           fun f l = ppList (List.map ppExpression l)
           fun g t = ppBracket (ppExpression t)
        in
           if Types.equalTy Type.stringTy ty
              then case listOfList t of
                      ([], _) => ppApp ("L3.prefix", ppExpression a)
                    | (l, NONE) =>
                        (case stringOfList l of
                            SOME s => ppQ s
                          | NONE => ppApp ("String.implode", f l))
                    | (l, SOME tm) =>
                         ppBL (0, 2, [ppApp ("String.implode", f l),
                                      ppS "^", g tm])
           else (case listOfList t of
                    ([], _) => ppApp ("(op ::)", ppExpression a)
                  | (l, NONE) => f l
                  | ([h], SOME tm) => ppBL (0, 2, [g h, ppS "::", g tm])
                  | (l, SOME tm) => ppBL (0, 2, [f l, ppS "@", g tm]))
        end
   | Term.Comb ("InitMap", ty, [a]) =>
       ppInitMap (Types.domain (Types.expand ty)) a
   | Term.Comb (f, ty, [a]) =>
       (case lookupOperation f of
          Consts.Primitive _ =>
           ppApp (ppMop (f, Term.typeOf a, ty), ppExpression a)
        | Consts.Destructor _ =>
           let
              fun err () = raise Fail "Constructor has wrong form"
              val aty = Term.primTypeOf a
              fun pa x = ppApp (x, ppExpression a)
           in
              if Types.isRecordType aty
                 then ppApp ("#" ^ f,
                             ppL (0, [ppBracket (ppExpression a), ppS " :",
                                      ppB (1, 0), ppType (Term.primTypeOf a)]))
              else if Types.isFixedBitsType aty andalso Types.isRecordType ty
                 then pa ("rec'" ^ f)
              else case Lib.total Types.destProd aty of
                     SOME (ty1, ty2) =>
                       if Types.equalTy ty1 ty
                          then if Types.isRecordType ty1
                                  then let
                                         val n =
                                           Type.destConstType (Types.expand ty1)
                                         val p = if n = "ieee_flags" then "SSE."
                                                 else ""
                                       in
                                         pa (p ^ n ^ "_" ^ f ^ "_rupd")
                                       end
                               else if Types.isFixedBitsType ty1 andalso
                                       Types.isRecordType ty2
                                  then pa ("write'rec'" ^ f)
                               else err ()
                       else err ()
                   | NONE => err ()
           end
        | Consts.Constructor _ =>
            (case ppRecord (f, ty, [a]) of
                SOME p => p
              | NONE => ppApp (renameReserved f, ppExpression a))
        | Consts.Accessor (rd, wr, _) =>
            let
               val aty = Term.primTypeOf a
               val rty = Term.primTypeOf rd
               val wty = Term.primTypeOf wr
               val fty = aty --> ty
               val (d, name) =
                  if Types.canMatch rty fty
                     then (rd, f)
                  else if Types.canMatch wty fty
                     then (wr, "write'" ^ f)
                  else if Types.canMatch (Type.unitTy --> rty) fty
                     then (rd, f) (* see makeImpureFunctional below *)
                  else ( Lib.pp (PolyML.prettyRepresentation (t, 10))
                       ; raise Fail "ppExpression: Accessor has bad type"
                       )
            in
               ppDefn name d [ppBracket (ppExpression a)] fty
            end
        | Consts.Definition (d, _, _) =>
            let
              val fty = Term.primTypeOf a --> ty
              val returnsmap =
                case Consts.lookupConst f of
                   Consts.Definition (d, _, _) =>
                      not (Term.isAbs d orelse Term.equalTm Term.unitTm a)
                 | _ => false
            in
              if returnsmap
                then ppExpression
                       (Term.Comb ("abs-apply", ty,
                                   [Term.Comb (f, fty, []), a]))
              else ppDefn (expandASTName f) d [ppBracket (ppExpression a)] fty
            end
        | Consts.Exception _ =>
            ppL (2, [ppS "raise ", ppS (Tag.remove f), ppB (1, 0),
                     ppBracket (ppExpression a)])
        | Consts.Undefined =>
            if String.isPrefix "boolify'" f
               then ( boolify :=
                         Lib.insert (String.extract (f, 8, NONE)) (!boolify)
                    ; ppApp (f, ppExpression a))
            else if f = "String.explode" orelse f = "String.implode"
               then ppApp (f, ppExpression a)
            else raise Fail ("ppExpression, undefined 1-arg: " ^ f))
   | Term.Comb (",", _, [a, b]) => ppPair (ppExpression a, ppExpression b)
   | Term.Comb (";", _, [_, _]) =>
       let
          val l = destSequence t
       in
          PolyML.PrettyBlock (0, true, [],
             ppS "( " ::
             mapSeparate I [ppB (0, 0), ppS "; "]
                (List.map (fn x => ppL (2, [ppExpression x])) l) @
             [ppB (1, 0), ppS ")"])
       end
   | Term.Comb ("and", _, [a, b]) =>
       ppInfix (ppExpression a, " andalso", ppExpression b)
   | Term.Comb ("or", _, [a, b]) =>
       ppInfix (ppExpression a, " orelse", ppExpression b)
   | Term.Comb ("==", ty, [a, b]) =>
       if Type.isSetTy (Term.typeOf a)
          then ppAppPair ("Set.equal", ppExpression a, ppExpression b)
       else ppInfix (ppExpression a, " =", ppExpression b)
   | Term.Comb ("<-", _, [Term.Var (a, _), b]) =>
       let
          val selfupdate =
             case b of
                Term.Comb ("update-map", _, [Term.Var (m, _), _, _]) => m = a
              | Term.Comb (d, _, [Term.Comb (",", _, [Term.Var (m, _), _])]) =>
                   m = a andalso Consts.isDestructor d
              | Term.Comb ("InitMap", _, _) => true
              | Term.Var (m, _) => m = a
              | _ => false
          val be = if selfupdate then ppExpression b else ppMapExpression b
       in
          ppInfix (ppR (reference a), " :=", be)
       end
   | Term.Comb ("var =", _, [Term.Var (a, _), b, c]) =>
       PolyML.PrettyBlock (0, true, [],
           [ppS "let",
            ppB (1, 2),
            ppL (0, [ppS "val ", ppR (reference a), ppS " = ref ",
                     ppBracket (ppMapExpression b)]),
            ppB (1, 0),
            ppS "in",
            ppB (1, 2),
            ppL (0, [ppExpression c]),
            ppB (1, 0),
            ppS "end"])
   | Term.Comb ("for", _, [a, b, c]) =>
       ppAppTriple ("L3.for", ppExpression a, ppExpression b, ppExpression c)
   | Term.Comb ("foreach", _, [a, b]) =>
       ppAppPair ("L3.foreach", ppExpression a, ppExpression b)
   | Term.Comb (":", ty, [a, b]) =>
       (case Term.destConcats t of
           [x, y] =>
             if Type.isListTy (Types.expand ty)
                then ppBL (0, 2, [ppBracket (ppExpression a),
                                  ppS (if Types.equalTy Type.stringTy ty
                                          then "^"
                                       else "@"),
                                  ppBracket (ppExpression b)])
             else ppApp ("BitsN.@@", ppPair (ppExpression a, ppExpression b))
         | l => if Type.isListTy (Types.expand ty)
                   then ppExpression
                      (Term.Comb ("Concat", ty,
                                  [Term.mkList (Lib.I, Type.listTy ty) l]))
                else ppApp ("BitsN.concat", ppList (List.map ppExpression l)))
   | Term.Comb ("^", ty, l as [a, b]) =>
       let
          fun pp s = ppAppPair (s, ppExpression a, ppExpression b)
       in
          case Types.dest ty of
             Type.Other "bitstring" => pp "Bitstring.replicate"
           | Type.FixedBits i =>
                pp ("BitsN.resize_replicate " ^ Int.toString i)
           | Type.VarBits (s, _) => pp ("BitsN.resize_replicate " ^ s)
           | _ => raise Fail ("ppExpression: " ^ PolyML.makestring t)
       end
   | Term.Comb (f, ty, l as [a, b]) =>
      (case ppRecord (f, ty, l) of
         SOME p => p
       | _ => ppAppPair (ppBop (f, Term.typeOf a, Term.typeOf b),
                         ppExpression a, ppExpression b))
   | Term.Comb (f, ty, l) =>
      (Option.valOf (ppRecord (f, ty, l))
       handle Option.Option =>
                raise Fail ("ppExpression: " ^ PolyML.makestring t))
   | _ => ( pp (PolyML.prettyRepresentation (t, 40))
          ; raise Fail "ppExpression: bad match")
and ppRecord (f, ty, l) =
   if Tag.isRecord f
      then let
              val name = Type.destConstType (Types.expand ty)
           in
              case Types.lookupConst name of
                 SOME {def = Types.Record r, ...} =>
                    let
                       val p =
                          List.map
                             (fn ((fld, _), e) =>
                                ppL (0,
                                  [ppS fld, ppS " =", ppB (1, 2),
                                   ppL (0, [ppExpression e])]))
                             (ListPair.zip (r, l))
                    in
                       SOME (ppParen ("{", [ppS ",", ppB (1, 0)], "}") p)
                    end
               | _ => raise Fail ("ppRecord: bad record type: " ^ f)
           end
   else NONE
and ppMatch (m, []) = raise Fail "ppMatch: empty cases"
  | ppMatch (m, [c]) =
   PolyML.PrettyBlock (0, true, [],
       [ppS "case ", ppExpression m, ppS " of",
        ppB (1, 3), ppCase "" c])
  | ppMatch (m, c :: cases) =
   PolyML.PrettyBlock (0, true, [],
       [ppS "case ", ppExpression m, ppS " of",
        ppB (1, 3), ppCase "" c, ppB (1, 1)] @
        mapSeparate I [ppB (1, 1)]
           (List.map (ppCase "| ") cases @
            (if Type.isFixedTy (Term.typeOf m) andalso not (List.null cases)
                andalso Term.isLit (fst (Term.destCase (List.last cases)))
               then [ppS "| _ => raise General.Bind"]
             else [])))
and ppCase s t =
   case t of
      Term.Comb ("case", _,
         [a as Term.Abs (_, _, Term.Comb (",", _, [_, _]))]) =>
         (case Term.destAbs a of
            (_, Term.Comb (",", _, [pat, c])) =>
               ppL (0, [ppS s, ppL (0, [ppPattern pat]),
                        ppS " =>", ppB (1, 2),
                        ppL (0, [(if isMatch c orelse isCond c
                                    then ppBracket
                                  else I) (ppExpression c)])])
          | _ => raise Fail "ppCase: abs")
    | Term.Comb ("case", _, [Term.Comb (",", _, [pat, c])]) =>
         ppL (0, [ppS s, ppL (0, [ppPattern pat]), ppS " =>",
                  ppB (1, 2), ppL (0, [(if isMatch c then ppBracket else I)
                                          (ppExpression c)])])
    | _ => raise Fail "ppCase"
and ppPattern t =
   case t of
      Term.Lit (Term.Other ("Nil", _)) => ppS "[]"
    | Term.Lit v => ppLiteral true v
    | Term.Var s_ty => ppVar s_ty
    | Term.Comb (",", _, [a, b]) => ppPair (ppPattern a, ppPattern b)
    | Term.Comb ("Cons", _, [_]) =>
        (case listOfList t of
            ([], _) => ( pp (PolyML.prettyRepresentation (t, 40))
                       ; raise Fail "ppPattern: Cons pat"
                       )
          | (l, NONE) => ppList (List.map ppPattern l)
          | (l, SOME tm) =>
              List.foldr (fn (h, t) => ppInfix (ppPattern h, " ::", t))
                 (ppPattern tm) l)
    | Term.Comb (x as (f, ty, [a])) =>
        (case lookupOperation f of
            Consts.Constructor _ =>
              (case ppRecord x of
                  SOME p => p
                | NONE => ppApp (renameReserved f, ppExpression a))
          | Consts.Primitive _ =>
              ppApp (ppMop (f, Term.typeOf a, ty), ppPattern a)
          | _ => raise Fail ("ppPattern 1-arg: " ^ f))
    | Term.Comb (f, ty, l) =>
       (Option.valOf (ppRecord (f, ty, l))
        handle Option.Option => raise Fail ("ppPattern: " ^ f))
    | _ => ( pp (PolyML.prettyRepresentation (t, 40))
           ; raise Fail "ppPattern: bad match")
and ppMapExpression t =
  (case t of
      Term.Lit _ => ppExpression t
    | Term.Abs _ => ppExpression t
    | Term.Comb ("InitMap", _, [_]) => ppExpression t
    | Term.Comb ("Some", _, [a]) => ppApp ("Option.SOME", ppMapExpression a)
    | Term.Comb (",", _, [a, b]) =>
      ppPair (ppMapExpression a, ppMapExpression b)
    | _ =>
      let
         val ty = Term.typeOf t
         val te = ppExpression t
      in
         if !safemap
            then case getMap ty of
                    BadMap =>
                      ( safemap := false
                      ; warn ("Reverting to PureMap.\n" ^ PolyML.makestring t)
                      ; te
                      )
                  | CopyMap pp =>
                      let
                        val te = ppBracket te
                        val n = case te of PolyML.PrettyString _ => 1 | _ => 0
                      in
                        ppL (2, [pp, ppB (n, 0), te])
                      end
                  | _ => te
         else te
      end)
and ppInitMap ty a =
   let
      val sz = mapSize ty
      val ae = ppExpression a
   in
      if sz = 0
         then ppApp ("L3.K", ae)
      else ppAppPair ("Map.mkMap",
                      ppS (if sz = ~1 then "NONE"
                           else "SOME " ^ (if sz = ~2
                                             then bvSizeString (Types.expand ty)
                                           else annotatedIntInf sz)), ae)
   end

(* - printing of global variables (state) and definitions -------------- *)

local
   fun ppGlobal (s, ty) =
      let
         val unk = ppExpression (Term.genUnknown ty)
      in
         ppL (0, [ppS "val", ppB (1, 2), ppR s, ppS " = ref", ppB (1, 2),
                  ppL (0, [ppL (1, [ppS "(", unk, ppS ")"])]), ppB (0, 2),
                  ppS ": ", ppBracket (ppType ty), ppS " ref"])
      end
   fun ppGlobalSig (s, ty) =
      ppL (0, [ppS "val", ppB (1, 2), ppR s, ppS ":",
               ppB (1, 2), ppBracket (ppType ty), ppS " ref"])
   fun pp f =
      List.mapPartial
        (fn (s, {typ, mutable = true}) => SOME (f (s, typ))
          | _ => NONE) o Env.listVariables o Env.get
in
   val ppGlobals = pp ppGlobal
   val ppGlobalsSig = pp ppGlobalSig
end

local
   fun v i = ppS ("t" ^ Int.toString i)
   fun ppTupleN name n =
      let
         val l = List.tabulate (n, v)
         val (x, y) = Lib.lastButlast l
         val p = List.foldr ppPair x y
         val z = PPInt.fromInt (String.size name) + 3
      in
         ppL (2, [ppS ("fun " ^ name ^ " "), ppL (z, [ppList l]), ppS " =",
                  ppB (1, 0), ppL (0, [p]), ppB (1, 0),
                  ppS ("| " ^ name ^ " (_: bool list) = raise Fail \"" ^
                       name ^ "\"")])
      end
in
   fun ppBoolifyN n =
      let
         val ns = Int.toString n
         val tuple = "tuple'" ^ ns
         val name = "boolify'" ^ ns
      in
         PolyML.PrettyBlock (0, true, [],
            [ppS "local", ppB (1, 2), ppTupleN tuple n, ppB (1, 0), ppS "in",
             ppB (1, 2),
             ppS ("val " ^ name ^ " = " ^ tuple ^ " o BitsN.toList"),
             ppB (1, 0), ppS "end"])
      end
   fun ppBoolifyNSig n =
      let
         val name = "boolify'" ^ (Int.toString n)
         val ty = Type.foldProdList (List.tabulate (n, fn _ => Type.boolTy))
      in
         PolyML.PrettyBlock (2, true, [],
            [ppS ("val " ^ name ^ ":"), ppB (1, 0),
             PolyML.PrettyBlock (0, false, [],
                [ppType (Type.fixedTy n), ppB (1, 0), ppS "->", ppB (1, 0),
                 ppType ty])])
      end
end

local
   fun dereference t =
     case t of
        Term.Lit _ => t
      | Term.BVar _ => t
      | Term.Var ("_", _) => t
      | Term.Var (a, aty) => Term.Var ("(!" ^ renameConsReserved a ^ ")", aty)
      | Term.Abs (l, ty, u) => Term.Abs (l, ty, dereference u)
      | Term.Comb (s, ty, l) => Term.Comb (s, ty, List.map dereference l)
   val condConv =
     fn Term.Comb ("i-t-e", _, [Term.Lit (Term.Bool true), a, _]) => a
      | Term.Comb
          ("i-t-e", _,
           [Term.Comb ("not", _, [Term.Lit (Term.Bool false)]), a, _]) => a
      | Term.Comb ("i-t-e", _, [Term.Lit (Term.Bool false), _, a]) => a
      | Term.Comb
          ("i-t-e", _,
           [Term.Comb ("not", _, [Term.Lit (Term.Bool true)]), _, a]) => a
      | _ => raise Term.NoConv
   val proverConv =
     fn Term.Var ("PROVER_EXPORT", _) => Term.Lit (Term.Bool false)
      | _ => raise Term.NoConv
in
   val conv = Convert.mergeAnonConv o dereference o
              Matches.stringExplodeMatches o Matches.boolifyMatches o
              Term.depthconv condConv o Term.depthconv proverConv
end

val makeImpureFunctional =
   Term.depthconv
      (fn t as Term.Comb (f, ty, []) =>
            if Stringset.member (!impure, expandASTName f) andalso
               noBitsTypeVars f
               then Term.Comb (f, ty, [Term.unitTm])
            else t
        | _ => raise Term.NoConv)

val isImpure =
   Option.isSome o
   Term.findTerm
      (fn Term.Var _ => true
        | Term.Comb (f, _, _) =>
           Tag.isException f orelse Stringset.member (!impure, expandASTName f)
        | _ => false)

fun ppDefinition (s, t) =
   let
      val vs = maybeTuple (bitsTypeVars t)
   in
      case t of
        Term.Abs _ =>
          let
             val (v, b) = Term.destAbs t
          in
             ppL (2, [ppS ("fun " ^ s), ppB (1, 0)] @ vs @
                     (if List.null vs then [] else [ppB (1, 0)]) @
                     [ppL (2, [ppPattern v]), ppS " =",
                      ppB (1, 0), ppExpression b, ppS ";"])
          end
      | _ =>
         if List.null vs
            then ppL (2, [ppS ("val " ^ s ^ " ="), ppB (1, 0),
                          ppExpression t])
         else ppL (2, [ppS ("fun " ^ s), ppB (1, 0)] @ vs @
                      [ppS " =", ppB (1, 0), ppExpression t, ppS ";"])
   end

fun ppDefinitions () =
   let
      val l =
         List.map
             (fn {name, def, ...} =>
                 let
                    val d = conv def
                    val is_impure = isImpure d
                    val () =
                       if is_impure
                          then impure := Stringset.add (!impure, name)
                       else ()
                    val d = makeImpureFunctional d
                    val d = if is_impure andalso not (Term.isAbs d) andalso
                               List.null (bitsTypeVars d)
                               then Term.absList [("_", Type.unitTy)] d
                            else d
                 in
                    ppDefinition (renameReserved name, d)
                 end)
            ( safemap := true
            ; boolify := []
            ; impure := Stringset.empty
            ; Consts.listDefinitions ()
            )
      val bs = List.mapPartial Int.fromString (!boolify)
   in
      List.map ppBoolifyN bs @ l
   end

fun ppDefinitionSig (s, t) =
   let
      val ty = case t of
                  Term.Abs (_, ty, _) =>
                    let
                       val (t1, t2) = Types.domainRange ty
                    in
                       ppInfix (ppType t1, " ->", ppType t2)
                    end
                | _ => ppType (Term.typeOf t)
      val vs = List.map (K Type.natTy) (bitsTypeVars t)
   in
      if List.null vs
         then ppL (2, [ppS ("val " ^ s ^ ":"), ppB (1, 0), ty])
      else ppL (2, [ppS ("val " ^ s ^ ":"), ppB (1, 0),
                    ppType (Type.foldProdList vs), ppB (1, 0), ppS "->",
                    ppB (1, 0), ty])
   end

fun ppDefinitionsSig () =
   let
      val l =
         List.map
            (fn {name, def = d, ...} =>
                 let
                    val is_impure =
                       Stringset.member (!impure, expandASTName name)
                    val d = if is_impure andalso not (Term.isAbs d) andalso
                               List.null (bitsTypeVars d)
                               then Term.absList [("_", Type.unitTy)] d
                            else d
                 in
                    ppDefinitionSig (renameReserved name, d)
                 end)
            (Consts.listDefinitions ())
      val bs = List.mapPartial Int.fromString (!boolify)
   in
      List.map ppBoolifyNSig bs @ l
   end

local
   val sep = Lib.mapSeparate I [PP.ppS "\n"]
   val line = String.implode (List.tabulate (73, fn _ => #"-"))
   val scomm = "\n(* " ^ line ^ "\n   "
   val fcomm = "\n   " ^ line ^ " *)\n\n"
   fun commentBlock s = if s = "" then [] else [ppS (scomm ^ s ^ fcomm)]
   fun block f s =
      let
         val l = f ()
      in
         if List.null l then [] else commentBlock s @ sep l
      end
   fun struct_functor name =
      if isFunctor () then "functor " ^ name ^ " ()" else "structure " ^ name
   fun insertSafeMap l =
      List.take (l, 3) @
      [ppS ("\nstructure Map = " ^
            (if !safemap then "MutableMap" else "PureMap") ^ "\n")] @
      List.drop (l, 3)
in
   fun ppStructure (name, date) =
      [ppS ("(* " ^ name ^ " - generated by L3 - " ^ date ^ " *)\n\n"),
       ppS (struct_functor name ^ " :> " ^ name ^ " =\n"),
       ppS "struct\n"] @
      block ppTypeDefs "Type declarations" @
      block ppTypeCasts "Casting maps (for enumerated types)" @
      block ppRecordUpdateFuns "Record update functions" @
      block ppExceptions "Exceptions" @
      block ppGlobals "Global variables (state)" @
      block ppDefinitions "Main specification" @
      [ppS "\nend"]
      |> insertSafeMap
   fun ppSignature (name, date) =
      [ppS ("(* " ^ name ^ " - generated by L3 - " ^ date ^ " *)\n\n"),
       ppS ("signature " ^ name ^ " =\n"),
       ppS "sig\n",
       ppS "\nstructure Map : Map\n"] @
      block ppTypeDefs "Types" @
      block ppExceptions "Exceptions" @
      commentBlock "Functions" @
      ppTypeCastsSig () @
      ppGlobalsSig () @
      ppRecordUpdateFunsSig () @
      ppDefinitionsSig () @
      [ppS "\nend"]
end

fun export s =
   let
      val {dir, file} = process_destination s
      val smlFile =
         OS.Path.joinDirFile
            {dir = dir,
             file = OS.Path.joinBaseExt {base = file, ext = SOME "sml"}}
      val sigFile =
         OS.Path.joinDirFile
            {dir = dir,
             file = OS.Path.joinBaseExt {base = file, ext = SOME "sig"}}
      val name_date = (file, Date.toString (Date.fromTimeLocal (Time.now ())))
   in
      savePP smlFile (ppStructure name_date)
    ; savePP sigFile (ppSignature name_date)
   end

fun spec (specfiles, path) = (Runtime.LoadF specfiles; export path)

end (* SMLExport *)

(* ------------------------------------------------------------------------ *)

(* Testing...

val () = SMLExport.spec ("examples/Thacker/tiny.spec", "sml/tiny")
val () = SMLExport.spec ("examples/mips/mips.spec", "sml/mips")
val () = SMLExport.spec ("examples/x86/x64.spec", "sml/x64")

val () =
   SMLExport.spec
     ("examples/arm7/arm-base.spec, examples/arm7/arm-vfp.spec,\
      \examples/arm7/arm-iset.spec, examples/arm7/arm-run.spec", "sml/arm")

val () =
   SMLExport.spec
     ("examples/arm7/arm-base.spec, examples/arm7/arm-vfp.spec,\
      \examples/arm7/arm-iset.spec, examples/arm7/arm-run.spec,\
      \examples/arm7/arm-encode.spec", "sml/arm")

val () =
   SMLExport.spec
      ("examples/6m/arm-base.spec, examples/6m/arm-iset.spec,\
       \examples/6m/arm-run.spec", "sml/m0")

val () = SMLExport.export "sml/test.sml"

*)
