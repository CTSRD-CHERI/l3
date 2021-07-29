(*
use "Export.sml";
*)

(* ------------------------------------------------------------------------
   Pretty-print S-expression code for generating types, terms and definitions
   ------------------------------------------------------------------------ *)

signature IL_PP =
sig
   val ppDefinitions :
     (Consts.defn -> (string * Term.term) option) -> PolyML.pretty list
   val ppTypeDefs : unit -> PolyML.pretty list
end

structure IL_PP :> IL_PP =
struct
   open PP

   fun ppExp l = ppBracket (ppL (2, Lib.mapSeparate ppBracket [ppB (1, 0)] l))

   val listOfTuple =
      let
         fun iter a =
            fn Type.Prod (l, r) => iter (l::a) r
             | x => x::a
      in
         List.rev o iter []
      end

   local
      open Type
      val param =
         fn ListTy => "list"
          | OptionTy => "option"
          | SetTy => "set"
      fun pp dty =
         case dty of
            VarType s => ppApp ("tyvar", ppS s)
          | BV i => ppApp ("bits", ppS (Int.toString i))
          | BVV s => ppApp ("bits", ppS s)
          | Prod _ => ppExp (ppS "prod" :: List.map pp (listOfTuple dty))
          | Arrow (a, b) => ppAppPair ("arrow", pp a, pp b)
          | ParamType (p, t) => ppApp (param p, pp t)
          | ConstType s => ppS s
   in
      fun ppType ty = pp (fst (Types.expand ty))
      fun ppBitsType ty =
        ppS (case fst (Types.expand ty) of
                BV i => Int.toString i
              | BVV s => s
              | _ => raise Fail "ppBitsType")
   end

   local
      fun ppTypeDefArg (name, d) =
         case d of
           Types.Constructors (Types.Enum m) =>
             let
                val l = m |> Stringmap.listItems
                          |> msort (Int.compare o (snd ## snd))
                          |> List.map (fn (n, _) => ppPair (ppS n, ppS "()"))
             in
                SOME (ppS "datatype" :: ppS name :: l)
             end
         | Types.Constructors (Types.Construct m) =>
             let
                val ppOTy = fn SOME ty => ppType ty
                             | NONE => ppS "()"
                val l = m |> Stringmap.listItems
                          |> List.map (fn (n, oty) => ppPair (ppS n, ppOTy oty))
             in
                SOME (ppS "datatype" :: ppS name :: l)
             end
         | Types.Record l =>
             let
                val l = List.map (fn (n, ty) => ppPair (ppS n, ppType ty)) l
             in
                SOME (ppS "record" :: ppS name :: l)
             end
         | _ => NONE

      fun ppTypeDef (n, d : Types.typeconst) =
         case ppTypeDefArg (n, #def d) of
           SOME l  => SOME (ppExp l)
         | NONE => NONE
   in
      fun ppTypeDefs () = List.mapPartial ppTypeDef (Types.listConsts ())
   end

   (* --------------------------------------------------------------------- *)

   local
      fun ppInt i = ppS (IntInf.toString i)
      val ppNat = ppInt o Nat.toInt
      fun ppChar c = ppS (if c = #"\\" then "\\"
                          else if Char.isPrint c then Char.toString c
                          else "\\" ^ Int.toString (Char.ord c))
   in
      val ppLiteral =
         fn Term.Bits w =>
               ppExp [ppS "bv", ppNat (BitsN.toNat w), ppNat (BitsN.size w)]
          | Term.Bitstring s => ppExp [ppS "bl", ppS (Bitstring.toBinString s)]
          | Term.Bool true => ppS "true"
          | Term.Bool false => ppS "false"
          | Term.Char c => ppExp [ppS "char", ppChar c]
          | Term.Enum (n, s) =>
              (let
                  val e = Option.valOf (Types.revenum s n)
               in
                  ppExp [ppS "const", ppS e, ppType (Type.mkConstType s)]
               end
               handle Option =>
                  raise Fail ("ppLiteral: Enum (" ^ Int.toString n ^ ", " ^ s))
          | Term.Int i => ppExp [ppS "int", ppInt i]
          | Term.Nat n => ppExp [ppS "nat", ppNat n]
          | Term.Other ("UNKNOWN", ty) => ppExp [ppS "unknown", ppType ty]
          | Term.Other (s, ty) =>
              (case fst (Types.expand ty) of
                  Type.BV 32 =>
                    (case s of
                        "FP32_NegInf" => ppS ("neginf32")
                      | "FP32_PosInf" => ppS ("posinf32")
                      | "FP32_NegZero" => ppS ("negzero32")
                      | "FP32_PosZero" => ppS ("poszero32")
                      | "FP32_NegMin" => ppS ("negmin32")
                      | "FP32_PosMin" => ppS ("posmin32")
                      | "FP32_NegMax" => ppS ("negmax32")
                      | "FP32_PosMax" => ppS ("posmax32")
                      | "FP32_qNan" => ppS ("qnan32")
                      | "FP32_sNan" => ppS ("snan32")
                      | _ => raise Fail ("ppLiteral: 32-bit " ^ s))
                | Type.BV 64 =>
                    (case s of
                        "FP64_NegInf" => ppS ("neginf64")
                      | "FP64_PosInf" => ppS ("posinf64")
                      | "FP64_NegZero" => ppS ("negzero64")
                      | "FP64_PosZero" => ppS ("poszero64")
                      | "FP64_NegMin" => ppS ("negmin64")
                      | "FP64_PosMin" => ppS ("posmin64")
                      | "FP64_NegMax" => ppS ("negmax64")
                      | "FP64_PosMax" => ppS ("posmax64")
                      | "FP64_qNan" => ppS ("qnan64")
                      | "FP64_sNan" => ppS ("snan64")
                      | _ => raise Fail ("ppLiteral: 32-bit " ^ s))
                | Type.BVV n =>
                    (ppExp
                       [ppS "bv",
                        ppInt (Option.valOf (IntExtra.fromLit (Tag.remove s))),
                        ppS n]
                     handle Option => raise Fail ("ppLiteral: BVV " ^ s))
                | _ =>
                    (case s of
                        "{}" => ppApp ("empty", ppType (Types.destParam ty))
                      | "Nil" => ppApp ("nil", ppType (Types.destParam ty))
                      | "None" => ppApp ("none", ppType (Types.destParam ty))
                      | _ => ppAppPair ("const", ppS s, ppType ty)))
          | Term.String s => ppExp [ppS "string", ppQ s]
          | Term.Unit => ppS "unit"
      end

   fun lookupOperation s =
      case Consts.lookupConst s of
         Consts.Definition (_, _, ~1) => Consts.Primitive []
       | c as Consts.Constructor _ =>
           if s = "Some" then Consts.Primitive [] else c
       | c => c

   val mopId =
      Stringset.fromList
        ["Abs", "Cardinality", "Difference", "Drop", "Element", "Fst", "Head",
         "IndexOf", "Intersect", "IsAlpha", "IsAlphaNum", "IsDigit",
         "IsHexDigit", "IsLower", "IsMember", "IsSome", "IsSpace", "IsSubset",
         "IsUpper", "Length", "Max", "Min", "Msb", "PadLeft", "PadRight",
         "QuotRem", "Remove", "RemoveDuplicates", "RemoveExcept", "SetOfList",
         "Size", "Snd", "Some", "Tail", "Take", "ToLower", "ToUpper", "Union",
         "Update", "ValOf"]

   val fpOp =
      Stringset.fromList
        ["Abs", "Add", "Add_", "Div", "Div_", "FromInt", "IsIntegral",
         "IsFinite", "IsNan", "IsNormal", "IsSignallingNan", "IsSubnormal",
         "IsZero", "Mul", "Mul_", "MulAdd", "MulAdd_", "MulSub", "MulSub_",
         "Neg", "RoundToIntegral", "Sqrt", "Sqrt_", "Sub", "Sub_", "ToInt"]

   val fpOpMap =
      fn "Compare" => SOME "cmp"
       | "Equal" => SOME "eq"
       | "GreaterThan" => SOME "gt"
       | "GreaterEqual" => SOME "ge"
       | "LessThan" => SOME "lt"
       | "LessEqual" => SOME "le"
       | r => if Stringset.member (fpOp, r) then SOME r else NONE

   fun fp s f =
      if String.isPrefix ("FP" ^ s ^ "_") f
         then Option.map (fn x => ppS ("(fp" ^ L3.lowercase x ^ " " ^ s ^ ")"))
                (fpOpMap (String.extract (f, 5, NONE)))
      else NONE

   fun ppMop (f, ty) =
      case f of
        "-" => ppS "neg"
      | "~" => ppS "bwnot"
      | "Concat" => ppS "flat"
      | "FromBinString" => ppS "bin"
      | "FromDecString" => ppS "dec"
      | "FromHexString" => ppS "hex"
      | "InitMap" => ppApp ("K1", ppType (Types.domain ty))
      | "Log2" => ppS "log"
      | "Reverse" => ppS "rev"
      | "SignExtend" => ppApp ("signextend", ppBitsType ty)
      | "SignedMax" => ppS "smax"
      | "SignedMin" => ppS "smin"
      | "ZeroExtend" => ppApp ("castto", ppType ty)
      | "not" => ppS "not"
      | "FP32_ToFP64" => ppS "fp32to64"
      | "FP64_ToFP32" => ppS "fp64to32"
      | "FP64_ToFP32_" => ppS "fp64to32_"
      | _ => if Stringset.member (mopId, f)
                then ppS (L3.lowercase f)
             else case fp "32" f of
                     SOME x => x
                   | NONE => (case fp "64" f of
                                 SOME x => x
                               | NONE => raise Fail ("ppMop: " ^ f))

   val ppBop =
      fn "#<<"        => "rol"
       | "#>>"        => "ror"
       | "&&"         => "bwand"
       | "*"          => "mul"
       | "**"         => "exp"
       | "+"          => "add"
       | "-"          => "sub"
       | "<"          => "lt"
       | "<+"         => "ult"
       | "<.>"        => "bit"
       | "<<"         => "lsl"
       | "<="         => "le"
       | "<=+"        => "ule"
       | ">"          => "gt"
       | ">+"         => "ugt"
       | ">="         => "ge"
       | ">=+"        => "uge"
       | ">>"         => "asr"
       | ">>+"        => "lsr"
       | "??"         => "bwxor"
       | "and"        => "and"
       | "div"        => "div"
       | "in"         => "in"
       | "insert"     => "insert"
       | "mod"        => "mod"
       | "or"         => "or"
       | "quot"       => "quot"
       | "rem"        => "rem"
       | "sdiv"       => "sdiv"
       | "smod"       => "smod"
       | "splitl"     => "splitl"
       | "splitr"     => "splitr"
       | "fields"     => "fields"
       | "tokens"     => "tokens"
       | "||"         => "bwor"
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
      | stringOfList l =
         let
            val l = List.map Term.destCharLit l
         in
            if List.all Char.isPrint l then SOME (String.implode l) else NONE
         end
         handle Fail _ => NONE

   val listOfTuple =
      let
         fun iter a =
            fn Term.Comb (",", _, [l, r]) => iter (l::a) r
             | tm => tm::a
      in
         List.rev o iter []
      end

   fun bv_bl ty s = (if Type.isWordTy (Types.expand ty) then "bv" else "bl") ^ s

   fun ppBExpression t = ppBracket (ppExpression t)
   and ppExpression t =
      case t of
        Term.Lit (v as Term.String s) =>
          if List.all Char.isPrint (String.explode s) then ppLiteral v
          else ppExpression (Term.expandStringLit t)
      | Term.Lit v => ppLiteral v
      | Term.Abs _ =>
          let
             val (v, b) = Term.destAbs t
          in
             ppExp [ppS "lambda", ppExpression v, ppExpression b]
          end
      | Term.Var ("_", ty) => ppExp [ppS "anonvar", ppType ty]
      | Term.Var (s, ty) => ppExp [ppS "var", ppS s, ppType ty]
      | Term.Comb ("abs-apply", _, [b1 as Term.Abs ([q], _, b2), e]) =>
          let
             val (v, b) =
                case b2 of
                  Term.Comb ("match", _, [Term.BVar (0, _), _]) =>
                     hd (snd (Term.destMatch b2))
                | _ => let val v = Term.Var q in (v, Term.apply b1 v) end
          in
             ppExp [ppS "let", ppExpression v, ppExpression e, ppExpression b]
          end
      | Term.Comb ("abs-apply", _, [f, x]) =>
          ppExp [ppS "comb", ppExpression f, ppExpression x]
      | Term.Comb ("i-t-e", _, [a, b, c]) =>
          ppExp [ppS "if", ppExpression a, ppExpression b, ppExpression c]
      | Term.Comb ("update-map", _, [a, b, c]) =>
          ppExp [ppS "update", ppExpression a, ppExpression b, ppExpression c]
      | Term.Comb ("<..>", ty, [h, l, a]) =>
          let
            val s = bv_bl ty "extract"
          in
            ppExp (ppS s :: (if s = "blextract" then [] else [ppType ty]) @
                   [ppExpression h, ppExpression l, ppExpression a])
          end
      | Term.Comb ("bit-field-insert", ty, [h, l, a, b]) =>
          ppExp [ppS (bv_bl ty "insert"), ppExpression h, ppExpression l,
                 ppExpression b, ppExpression a]
      | Term.Comb ("{..}", _, l) =>
          ppExp (ppS "set" :: List.map ppExpression l)
      | Term.Comb ("[..]", ty, [a]) =>
          if Types.equalTy ty (Term.primTypeOf a)
             then ppExpression a
          else ppExp [ppS "apply", ppExp [ppS "castto", ppType ty],
                      ppExpression a]
      | Term.Comb ("match", ty, m::l) => ppMatch (m, l)
      | Term.Comb (f, ty, []) =>
           let
              val name = if Tag.isAST f then "dfn'" ^ Tag.remove f else f
              fun c () = ppExp [ppS "const", ppS name, ppType ty]
           in
              case Consts.lookupConst f of
                 Consts.Accessor _ => c ()
               | Consts.Definition _ => c ()
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
              ppExp [ppS "apply", ppS n, ppExpression a]
           end
      | Term.Comb ("m'for", _, [a]) =>
           let
              val (a, (b, c)) = Term.destTriple a
           in
              ppExp [ppS "for", ppExpression a, ppExpression b, ppExpression c]
           end
      | Term.Comb ("m'foreach", _, [a]) =>
           let
              val (a, b) = Term.destPair a
           in
              ppExp [ppS "foreach", ppExpression a, ppExpression b]
           end
      | Term.Comb ("Cons", _, [a]) =>
          (case listOfList t of
              ([], _) => ppExp [ppS "apply", ppS "cons", ppExpression a]
            | (l, NONE) =>
                (case stringOfList l of
                    SOME s => ppExp [ppS "string", ppQ s]
                  | NONE => ppExp (ppS "list" :: List.map ppExpression l))
            | (l, SOME tm) =>
                 ppExp [ppS "concat",
                        ppExp (ppS "list" :: List.map ppExpression l),
                        ppExp [ppS "apply", ppS "cons", ppExpression tm]])
      | Term.Comb (f, ty, [a]) =>
          (case lookupOperation f of
             Consts.Primitive _ =>
               ppExp [ppS "apply", ppMop (f, ty), ppBExpression a]
           | Consts.Destructor _ =>
              let
                 fun err () = raise Fail "Constructor has wrong form"
                 val aty = Term.primTypeOf a
                 fun pt (x, y) = ppExp [ppS x, ppS (y ^ f), ppExpression a]
              in
                 if Types.isRecordType aty
                    then pt ("recordlookup", "")
                 else if Types.isFixedBitsType aty andalso Types.isRecordType ty
                    then pt ("apply", "rec'")
                 else case Lib.total Types.destProd aty of
                        SOME (ty1, ty2) =>
                          if Types.equalTy ty1 ty
                             then if Types.isRecordType ty1
                                     then ppExp [ppS "recordupdate", ppS f,
                                                 ppExpression a]
                                  else if Types.isFixedBitsType ty1 andalso
                                          Types.isRecordType ty2
                                     then pt ("apply", "write'rec'")
                                  else err ()
                          else err ()
                      | NONE => err ()
              end
           | Consts.Constructor _ =>
               (case ppRecord (f, ty, [a]) of
                  SOME p => p
                | NONE =>
                    ppExp [ppS "apply+", ppS f, ppType ty, ppBExpression a])
           | Consts.Accessor (rd, wr, _) =>
               let
                  val aty = Term.primTypeOf a
                  fun canMatch tm =
                    Types.canMatch (Types.domain (Term.primTypeOf tm)) aty
                    handle Fail "domain" => false
                  val n =
                    if canMatch rd then f
                    else if canMatch wr then "write'" ^ f
                    else raise Fail "Accessor has bad type"
               in
                  ppExp [ppS "apply+", ppS n, ppType ty, ppBExpression a]
               end
           | Consts.Definition _ =>
               let
                  val name = if Tag.isAST f then "dfn'" ^ Tag.remove f else f
               in
                  ppExp [ppS "apply+", ppS name, ppType ty, ppBExpression a]
               end
           | Consts.Undefined =>
               if String.isPrefix "boolify'" f
                  then let
                          val i = String.extract (f, 8, NONE)
                       in
                          ppExp [ppS "totuple", ppS i, ppExpression a]
                       end
               else raise Fail ("ppExpression, undefined 1-arg: " ^ f)
           | _ =>  raise Fail ("ppExpression, 1-arg: " ^ f))
      | Term.Comb ("==", _, [a, b]) =>
          ppExp [ppS "apply", ppS "==", ppBExpression a, ppBExpression b]
      | Term.Comb (",", _, [_, _]) =>
          ppExp (ppS "tuple" :: List.map ppBExpression (listOfTuple t))
      | Term.Comb (":", _, [_, _]) =>
          ppExp (ppS "concat" :: List.map ppExpression (Term.destConcats t))
      | Term.Comb ("^", ty, [a, b]) =>
          ppAppTriple ("apply", ppS "repeat", ppExpression a, ppExpression b)
      | Term.Comb (f, ty, l as [a, b]) =>
         (case ppRecord (f, ty, l) of
            SOME p => p
          | _ => ppExp [ppS "apply", ppS (ppBop f), ppExpression a,
                        ppExpression b])
      | Term.Comb (f, ty, l) =>
         (Option.valOf (ppRecord (f, ty, l))
          handle Option.Option => raise Fail ("ppExpression: " ^ f))
      | _ => (pp (PolyML.prettyRepresentation (t, 40))
              ; raise Fail "ppExpression: bad match")
   and ppMatch (m, cases) =
      ppExp (ppS "case" :: ppBExpression m :: List.map ppCase cases)
   and ppCase t =
      case t of
        Term.Comb ("case", _,
           [a as Term.Abs (_, _, Term.Comb (",", _, [_, _]))]) =>
           (case Term.destAbs a of
              (_, Term.Comb (",", _, [pat, c])) =>
                 ppPair (ppExpression pat, ppExpression c)
            | _ => raise Fail "ppCase: abs")
      | Term.Comb ("case", _, [Term.Comb (",", _, [pat, c])]) =>
          ppPair (ppExpression pat, ppExpression c)
      | _ => raise Fail "ppCase"
   and ppRecord (f, ty, l) =
      if Tag.isRecord f
         then SOME
                (ppExp (ppS "record" :: ppType ty :: List.map ppExpression l))
      else NONE

   fun ppDefinition (s, t) =
     case t of
       Term.Abs _ =>
         let
            val (v, b) = Term.destAbs t
         in
            ppExp [ppS "def", ppS s, ppExpression v, ppExpression b]
         end
     | _ => ppExp [ppS "def", ppS s, ppS "()", ppExpression t]

   fun ppDefinitions conv =
      List.mapPartial (Option.compose (ppDefinition, conv))
         (Consts.listDefinitions ())

end (* IL_PP *)

(* ------------------------------------------------------------------------
   Export L3 specifications to S-expression intermediate language
   ------------------------------------------------------------------------ *)

signature ILExport =
sig
   val spec : string * string -> unit
   val export : string -> unit
end

structure ILExport :> ILExport =
struct

local
   val monadTerm =
      fn Term.Comb ("m'const", _, [_]) => true
       | Term.Comb ("m'bind", _, [_]) => true
       | Term.Comb ("m'read", _, [_]) => true
       | Term.Comb ("m'write", _, [_]) => true
       | Term.Comb ("m'extend", _, [_]) => true
       | Term.Comb ("m'unextend", _, [_]) => true
       | Term.Var ("_", _) => false
       | Term.Var _ => true
       | _ => false
   fun isOkay tm =
      case Term.findTerm monadTerm tm of
         SOME t => ( print "\n"
                   ; Lib.pp (PolyML.prettyRepresentation (t, 10))
                   ; false)
       | NONE => true
   val sConv =
     Convert.simpConv true false o Convert.boolMatchConv o
     Matches.boolifyMatches
   fun popt c b a = print (if b then a else c)
   val popt0 = popt ""
in
   fun conv () =
      let
         val width = 44
         val (mutable, s) = Monad.init ()
         val sty = Type.mkConstType s
         val mdfy = Monadify.monadifyDefn (mutable, sty)
         val dmdfy = Monadify.deMonadifyDefn sty
         fun transform (name, def, recursive) =
            let
               val ty = Term.primTypeOf def
               val m = mdfy (name, def, recursive)
               val ty = Term.primTypeOf def
               val ismonadic = Monad.isMonadic (name, ty)
               val isfun = Monad.isFunctional (name, ty)
               val ispure = Monad.isPure (name, ty)
               val d = if ismonadic
                         then ((if ispure then Lib.I
                                else Convert.simplifyMonadicConv isfun) o
                                Monadify.deMonadifyDefn sty ispure) m
                       else m
               val r = sConv d
            in
               Monad.removeMonadic (name, ty) (not (ispure andalso ismonadic))
             ; (r, isOkay r, isfun)
            end
      in
         fn {user, name, def, recursive, ...} : Consts.defn =>
            let
               fun hasPrefix x = String.isPrefix x name
               val x = List.tabulate (width - String.size name, K #".")
                       handle General.Size => []
            in
               print (name ^ " " ^ String.implode x ^ " ");
               if hasPrefix "m'"
                  then NONE before printn "skip."
               else if user
                  then let
                          val (r, ok, isfun) = transform (name, def, recursive)
                          val () = popt "bad" ok "ok"
                          val () = popt0 recursive "-rec"
                          val () = popt0 isfun "-fun"
                          val () = printn "."
                       in
                          SOME (name, r)
                       end
               else SOME (name, def) before printn "sys."
            end
      end
end

fun export name =
   let
      val () = Monad.stateName ("state")
      val cnv = conv ()
      val defs = IL_PP.ppDefinitions cnv
      val l = Lib.mapSeparate I [PP.ppS "\n"] (IL_PP.ppTypeDefs () @ defs)
   in
      PP.savePP (name ^ ".l3") l
      ; printn "Done."
   end

fun spec (specfiles, name) =
   (Runtime.LoadF specfiles; PP.sExpExport true; export name)

end (* structure ILExport *)
