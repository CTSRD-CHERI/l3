(*
export L3LIBDIR=lib
use "Export.sml";
*)

(* ------------------------------------------------------------------------
   Pretty-print HOL4 code for generating types, terms and definitions
   ------------------------------------------------------------------------ *)

signature HolPP =
sig
   val ppDefinitions :
     (Consts.defn -> (string * Term.term * Consts.measure) option) ->
     PolyML.pretty list
   val ppTypeDefs : unit -> PolyML.pretty list
end

structure HolPP :> HolPP =
struct
   open PP

   local
      open Type
      val fxTys = [1,4,8,16,32,64]
      val param =
         fn ListTy => "LTy"
          | OptionTy => "OTy"
          | SetTy => "STy"
      fun pp dty =
         case dty of
            VarType s => ppS ("VTy" ^ quote s)
          | ConstType "unit" => ppS "uTy"
          | ConstType "int"  => ppS "iTy"
          | ConstType "nat"  => ppS "nTy"
          | ConstType "bool" => ppS "bTy"
          | ConstType "char" => ppS "cTy"
          | ConstType "ieee_compare" => ppS "oTy"
          | ConstType "ieee_flags" => ppS "fTy"
          | ConstType "ieee_rounding" => ppS "rTy"
          | BV i =>
              let
                 val s = Int.toString i
              in
                 if Lib.mem i fxTys
                    then ppS ("F" ^ s)
                 else ppApp ("FTy", ppS s)
              end
          | BVV s => ppS ("BTy" ^ quote s)
          | Prod (a, b)  => ppAppPair ("PTy", pp a, pp b)
          | Arrow (a, b) => ppAppPair ("ATy", pp a, pp b)
          | ParamType (ListTy, ConstType "char") => ppS "sTy"
          | ParamType (ListTy, ConstType "bool") => ppS "vTy"
          | ParamType (p, t) => ppApp (param p, pp t)
          | ConstType s =>
              if (s = Monad.state () handle Option.Option => false)
                 then ppS "qTy"
              else ppS ("CTy" ^ quote s)
   in
      fun ppType ty = pp (fst (Types.expand ty))
   end

   local
      fun ppTypeDefArg (name, d) =
         case d of
           Types.Constructors (Types.Enum m) =>
             let
                val l = m |> Stringmap.listItems
                          |> msort (Int.compare o (snd ## snd))
                          |> List.map (fn (n, _) => ppPair (ppQ n, ppS "[]"))
             in
                SOME (true, ppPair (ppQ name, ppList l))
             end
         | Types.Constructors (Types.Construct m) =>
             let
                val ppOTy = fn SOME ty => ppList [ppType ty]
                             | NONE => ppS "[]"
                val l = m |> Stringmap.listItems
                          |> List.map (fn (n, oty) => ppPair (ppQ n, ppOTy oty))
             in
                SOME (true, ppPair (ppQ name, ppList l))
             end
         | Types.Record l =>
             let
                val l = List.map (fn (n, ty) => ppPair (ppQ n, ppType ty)) l
             in
                SOME (false, ppPair (ppQ name, ppList l))
             end
         | _ => NONE

      fun ppConstruct l = ppApp ("val _ = Construct", ppList l)
      fun ppRecord l = ppApp ("val _ = Record", l)

      fun ppTypeDef (n, d : Types.typeconst) =
         case ppTypeDefArg (n, #def d) of
           SOME (true, pp)  => SOME (ppConstruct [pp])
         | SOME (false, pp) => SOME (ppRecord pp)
         | NONE => NONE
   in
      fun ppTypeDefs () = List.mapPartial ppTypeDef (Types.listConsts ())
   end

   (* --------------------------------------------------------------------- *)

   local
      fun ppChar c = ppS ("#\"" ^ Char.toString c ^ "\"")
      fun ppInt i = ppS (IntInf.toString i)
      val ppNat = ppInt o Nat.toInt
   in
      val ppLiteral =
         fn Term.Bits w =>
               ppAppPair ("LW", ppNat (BitsN.toNat w), ppNat (BitsN.size w))
          | Term.Bitstring s =>
               ppL (1, [ppS "LV", ppQ (Bitstring.toBinString s)])
          | Term.Bool true => ppS "LT"
          | Term.Bool false => ppS "LF"
          | Term.Char c => ppL (1, [ppS "LSC", ppB (1, 0), ppChar c])
          | Term.Enum (n, s) =>
              (let
                  val e = Option.valOf (Types.revenum s n)
               in
                  if Lib.mem e ["roundTiesToEven", "roundTowardPositive",
                                "roundTowardNegative", "roundTowardZero"]
                     then ppS ("binary_ieeeSyntax." ^ e ^ "_tm")
                  else if Lib.mem e ["FP_LT", "FP_EQ", "FP_GT", "FP_UN"]
                     then ppS ("binary_ieeeSyntax." ^
                               String.extract (e, 3, NONE) ^ "_tm")
                  else ppAppPair ("LC", ppQ e, ppType (Type.mkConstType s))
               end
               handle Option =>
                  raise Fail ("ppLiteral: Enum (" ^ Int.toString n ^ ", " ^ s))
          | Term.Int i => ppL (1, [ppS "LI", ppB (1, 0), ppInt i])
          | Term.Nat n => ppL (1, [ppS "LN", ppB (1, 0), ppNat n])
          | Term.Other ("UNKNOWN", ty) => ppApp ("LX", ppType ty)
          | Term.Other (s, ty) =>
              (case fst (Types.expand ty) of
                  Type.BV 32 =>
                    (case s of
                        "FP32_NegInf" => ppS ("NEGINF32")
                      | "FP32_PosInf" => ppS ("POSINF32")
                      | "FP32_NegZero" => ppS ("NEGZERO32")
                      | "FP32_PosZero" => ppS ("POSZERO32")
                      | "FP32_NegMin" => ppS ("NEGMIN32")
                      | "FP32_PosMin" => ppS ("POSMIN32")
                      | "FP32_NegMax" => ppS ("NEGMAX32")
                      | "FP32_PosMax" => ppS ("POSMAX32")
                      | "FP32_qNan" => ppS ("QUIETNAN32")
                      | "FP32_sNan" => ppS ("SIGNALNAN32")
                      | _ => raise Fail ("ppLiteral: 32-bit " ^ s))
                | Type.BV 64 =>
                    (case s of
                        "FP64_NegInf" => ppS ("NEGINF64")
                      | "FP64_PosInf" => ppS ("POSINF64")
                      | "FP64_NegZero" => ppS ("NEGZERO64")
                      | "FP64_PosZero" => ppS ("POSZERO64")
                      | "FP64_NegMin" => ppS ("NEGMIN64")
                      | "FP64_PosMin" => ppS ("POSMIN64")
                      | "FP64_NegMax" => ppS ("NEGMAX64")
                      | "FP64_PosMax" => ppS ("POSMAX64")
                      | "FP64_qNan" => ppS ("QUIETNAN64")
                      | "FP64_sNan" => ppS ("SIGNALNAN64")
                      | _ => raise Fail ("ppLiteral: 32-bit " ^ s))
                | Type.BVV n =>
                    (ppAppPair
                        ("LY",
                         ppInt (Option.valOf (IntExtra.fromLit (Tag.remove s))),
                         ppQ n)
                     handle Option => raise Fail ("ppLiteral: BVV " ^ s))
                | _ =>
                    (case s of
                        "{}" => ppApp ("LE", ppType (Types.destParam ty))
                      | "Nil" => ppApp ("LNL", ppType (Types.destParam ty))
                      | "None" => ppApp ("LO", ppType (Types.destParam ty))
                      | _ => ppAppPair ("Const", ppQ s, ppType ty)))
          | Term.String s =>
              ppL (1, [ppS "LS", ppB (0, 0), ppQ (String.toString s)])
          | Term.Unit => ppS "LU"
      end

   fun lookupOperation s =
      case Consts.lookupConst s of
         Consts.Definition (_, _, ~1) => Consts.Primitive []
       | c as Consts.Constructor _ =>
           if s = "Some" then Consts.Primitive [] else c
       | c => c

   val mopId =
      Stringset.fromList
        ["Cardinality", "IsAlpha", "IsSpace", "RemoveExcept", "Size", "Abs",
         "Difference", "Drop", "Element", "Fst", "Head", "IndexOf",
         "Intersect", "IsAlphaNum", "IsDigit", "IsHexDigit", "IsLower",
         "IsMember", "IsSome", "IsSubset", "IsUpper", "Length", "Max", "Min",
         "Msb", "QuotRem", "Remove", "RemoveDuplicates", "Snd", "Some", "Tail",
         "Take", "ToLower", "ToUpper", "Union", "Update", "ValOf"]

   val fpOp =
      Stringset.fromList
        ["Abs", "Add", "Add_", "Div", "Div_", "FromInt", "IsIntegral",
         "IsFinite", "IsNan", "IsNormal", "IsSignallingNan", "IsSubnormal",
         "IsZero", "Mul", "Mul_", "MulAdd", "MulAdd_", "MulSub", "MulSub_",
         "Neg", "RoundToIntegral", "Sqrt", "Sqrt_", "Sub", "Sub_", "ToInt"]

   val fpOpMap =
      fn "Compare" => SOME "Cmp"
       | "Equal" => SOME "Eq"
       | "GreaterThan" => SOME "Gt"
       | "GreaterEqual" => SOME "Ge"
       | "LessThan" => SOME "Lt"
       | "LessEqual" => SOME "Le"
       | r => if Stringset.member (fpOp, r) then SOME r else NONE

   fun fp s f =
      if String.isPrefix ("FP" ^ s ^ "_") f
         then Option.map (fn x => ppS ("FP" ^ x ^ " " ^ s))
                (fpOpMap (String.extract (f, 5, NONE)))
      else NONE

   fun ppMop (f, ty) =
      case f of
        "-" => ppS "Neg"
      | "~" => ppS "BNot"
      | "PadLeft" => ppS "PadLeft"
      | "PadRight" => ppS "PadRight"
      | "Concat" => ppS "Flat"
      | "FromBinString" => ppS "Bin"
      | "FromDecString" => ppS "Dec"
      | "FromHexString" => ppS "Hex"
      | "InitMap" => ppApp ("K1", ppType (Types.domain ty))
      | "Log2" => ppS "Log"
      | "Reverse" => ppS "Rev"
      | "SetOfList" => ppS "SofL"
      | "SignExtend" => ppApp ("SE", ppType ty)
      | "SignedMax" => ppS "Smax"
      | "SignedMin" => ppS "Smin"
      | "ZeroExtend" => ppApp ("Cast", ppType ty)
      | "not" => ppS "Not"
      | "FP32_ToFP64" => ppS "FP32To64"
      | "FP64_ToFP32" => ppS "FP64To32"
      | "FP64_ToFP32_" => ppS "FP64To32_"
      | _ => if Stringset.member (mopId, f)
                then ppS f
             else case fp "32" f of
                     SOME x => x
                   | NONE => (case fp "64" f of
                                 SOME x => x
                               | NONE => raise Fail ("ppMop: " ^ f))

   val ppBop =
      fn "#<<"        => "Rol"
       | "#>>"        => "Ror"
       | "&&"         => "BAnd"
       | "*"          => "Mul"
       | "**"         => "Exp"
       | "+"          => "Add"
       | "-"          => "Sub"
       | "<"          => "Lt"
       | "<+"         => "Ult"
       | "<.>"        => "Bit"
       | "<<"         => "Lsl"
       | "<="         => "Le"
       | "<=+"        => "Ule"
       | ">"          => "Gt"
       | ">+"         => "Ugt"
       | ">="         => "Ge"
       | ">=+"        => "Uge"
       | ">>"         => "Asr"
       | ">>+"        => "Lsr"
       | "??"         => "BXor"
       | "and"        => "And"
       | "div"        => "Div"
       | "in"         => "In"
       | "insert"     => "Insert"
       | "mod"        => "Mod"
       | "or"         => "Or"
       | "quot"       => "Quot"
       | "rem"        => "Rem"
       | "sdiv"       => "SDiv"
       | "smod"       => "SMod"
       | "splitl"     => "Splitl"
       | "splitr"     => "Splitr"
       | "fields"     => "Fld"
       | "tokens"     => "Tok"
       | "||"         => "BOr"
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

   val listOfTuple =
      let
         fun iter a =
            fn Term.Comb (",", _, [l, r]) => iter (l::a) r
             | tm => tm::a
      in
         List.rev o iter []
      end

   fun ppExpression t =
      case t of
        Term.Lit v => ppLiteral v
      | Term.Abs _ =>
          let
             val (v, b) = Term.destAbs t
          in
             ppAppPair ("Close", ppExpression v, ppExpression b)
          end
      | Term.Var ("_", ty) =>
          ppApp ("AVar", ppType ty)
      | Term.Var (s, ty) =>
         (case Types.dest ty of
            Type.Other "unit" => ppS ("uVar" ^ quote s)
          | Type.Other "bool" => ppS ("bVar" ^ quote s)
          | Type.Other "nat" => ppS ("nVar" ^ quote s)
          | Type.Other "int" => ppS ("iVar" ^ quote s)
          | Type.Other "string" => ppS ("sVar" ^ quote s)
          | Type.Other "bitstring" => ppS ("vVar" ^ quote s)
          | Type.Other name =>
               if (name = Monad.state () handle Option.Option => false)
                  then ppS ("qVar" ^ quote s)
               else ppAppPair ("Var", ppQ s, ppType ty)
          | _ => ppAppPair ("Var", ppQ s, ppType ty))
      | Term.Comb ("abs-apply", _, [b1 as Term.Abs ([q], _, b2), e]) =>
          let
             val (v, b) =
                case b2 of
                  Term.Comb ("match", _, [Term.BVar (0, _), _]) =>
                     hd (snd (Term.destMatch b2))
                | _ => let val v = Term.Var q in (v, Term.apply b1 v) end
          in
             ppAppTriple ("Let", ppExpression v, ppExpression e,
                          ppExpression b)
          end
      | Term.Comb ("abs-apply", _, [f, x]) =>
          ppAppPair ("Apply", ppExpression f, ppExpression x)
      | Term.Comb ("i-t-e", _, [_, _, _]) =>
          (case Term.destIfThens t of
              ([(a, b)], c) =>
                ppAppTriple
                  ("ITE", ppExpression a, ppExpression b, ppExpression c)
            | (l, e) =>
                let
                   val its =
                      List.map (ppPair o (ppExpression ## ppExpression)) l
                in
                   ppAppPair ("ITB", ppList its, ppExpression e)
                end)
      | Term.Comb ("update-map", _, [a, b, c]) =>
          ppAppTriple ("Fupd", ppExpression a, ppExpression b, ppExpression c)
      | Term.Comb ("<..>", ty, [h, l, a]) =>
          ppAppQuad ("EX", ppExpression a, ppExpression h, ppExpression l,
                     ppType ty)
      | Term.Comb ("bit-field-insert", _, [h, l, a, b]) =>
          ppAppQuad ("BFI", ppExpression h, ppExpression l, ppExpression b,
                     ppExpression a)
      | Term.Comb ("{..}", _, l) =>
          ppL (2, [ppS "SL", ppList (List.map ppExpression l)])
      | Term.Comb ("[..]", ty, [a]) =>
          if Types.equalTy ty (Term.primTypeOf a)
             then ppExpression a
          else ppAppPair ("Mop", ppApp ("Cast", ppType ty), ppExpression a)
      | Term.Comb ("match", ty, m::l) =>
          ppMatch (m, l)
      | Term.Comb (f, ty, []) =>
           let
              val name = if Tag.isAST f then "dfn'" ^ Tag.remove f else f
              fun c () = ppAppPair ("Const", ppQ name, ppType ty)
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
              ppAppTriple ("Call", ppQ n, ppType ty, ppExpression a)
           end
      | Term.Comb ("m'const", _, [a]) =>
          ppAppPair ("MU", ppExpression a, ppType (Monad.stateOf t))
      | Term.Comb ("m'read", _, [a])    => ppApp ("MR", ppExpression a)
      | Term.Comb ("m'write", _, [a])   => ppApp ("MW", ppExpression a)
      | Term.Comb ("m'for", _, [a])     => ppApp ("For", ppExpression a)
      | Term.Comb ("m'foreach", _, [a]) => ppApp ("Foreach", ppExpression a)
      | Term.Comb ("m'bind", _, [a]) =>
          let
             val (l, r) = Term.destPair a
          in
             ppAppPair ("MB", ppExpression l, ppExpression r)
          end
      | Term.Comb ("m'extend", _, [a]) =>
          let
             val (l, r) = Term.destPair a
          in
             ppAppPair ("MN", ppExpression l, ppExpression r)
          end
      | Term.Comb ("m'unextend", ty, [a]) =>
          let
             val ety = fst (Types.destProd (snd (Monad.destMonadTy ty)))
          in
             ppAppPair ("MD", ppExpression a, ppType ety)
          end
      | Term.Comb ("Cons", _, [a]) =>
          (case listOfList t of
              ([], _) => ppAppPair ("LLC", ppS "[]", ppExpression a)
            | (l, NONE) =>
                (case stringOfList l of
                    SOME s => ppL (1, [ppS "LS", ppB (0, 0), ppQ s])
                  | NONE =>
                      ppL (2, [ppS "LL", ppList (List.map ppExpression l)]))
            | (l, SOME tm) =>
                 ppAppPair ("LLC", ppList (List.map ppExpression l),
                            ppExpression tm))
      | Term.Comb (f, ty, [a]) =>
          (case lookupOperation f of
             Consts.Primitive _ =>
               ppAppPair ("Mop", ppMop (f, ty), ppExpression a)
           | Consts.Destructor _ =>
              let
                 fun err () = raise Fail "Constructor has wrong form"
                 val aty = Term.primTypeOf a
                 val pa = ppExpression a
                 fun pt (x, y) = ppAppTriple (x, ppQ (y ^ f), ppType ty, pa)
              in
                 if Types.isRecordType aty
                    then pt ("Dest", "")
                 else if Types.isFixedBitsType aty andalso Types.isRecordType ty
                    then pt ("Call", "rec'")
                 else case Lib.total Types.destProd aty of
                        SOME (ty1, ty2) =>
                          if Types.equalTy ty1 ty
                             then if Types.isRecordType ty1
                                     then ppAppPair ("Rupd", ppQ f, pa)
                                  else if Types.isFixedBitsType ty1 andalso
                                          Types.isRecordType ty2
                                     then pt ("Call", "write'rec'")
                                  else err ()
                          else err ()
                      | NONE => err ()
              end
           | Consts.Constructor _ =>
               (case ppRecord (f, ty, [a]) of
                  SOME p => p
                | NONE => ppAppTriple ("Call", ppQ f, ppType ty,
                                       ppExpression a))
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
                  ppAppTriple ("Call", ppQ n, ppType ty, ppExpression a)
               end
           | Consts.Definition _ =>
               let
                  val name = if Tag.isAST f then "dfn'" ^ Tag.remove f else f
               in
                  ppAppTriple ("Call", ppQ name, ppType ty, ppExpression a)
               end
           | Consts.Undefined =>
               if String.isPrefix "boolify'" f
                  then let
                          val i = String.extract (f, 8, NONE)
                       in
                          ppAppPair ("BL", ppS i, ppExpression a)
                       end
               else raise Fail ("ppExpression, undefined 1-arg: " ^ f)
           | _ =>  raise Fail ("ppExpression, 1-arg: " ^ f))
      | Term.Comb ("==", _, [a, b]) =>
          ppAppPair ("EQ", ppExpression a, ppExpression b)
      | Term.Comb (",", _, [_, _]) =>
          ppApp ("TP", ppList (List.map ppExpression (listOfTuple t)))
      | Term.Comb (":", _, [_, _]) =>
          ppL (2,
               [ppS "CC", ppList (List.map ppExpression (Term.destConcats t))])
      | Term.Comb ("^", ty, [a, b]) =>
         (case Types.dest ty of
             Type.Other "bitstring" =>
                ppAppTriple ("Bop", ppS "Rep", ppExpression a, ppExpression b)
           | _ =>
                ppAppTriple ("REP", ppExpression a, ppExpression b, ppType ty))
      | Term.Comb (f, ty, l as [a, b]) =>
         (case ppRecord (f, ty, l) of
            SOME p => p
          | _ => ppAppTriple ("Bop", ppS (ppBop f), ppExpression a,
                              ppExpression b))
      | Term.Comb (f, ty, l) =>
         (Option.valOf (ppRecord (f, ty, l))
          handle Option.Option => raise Fail ("ppExpression: " ^ f))
      | _ => (pp (PolyML.prettyRepresentation (t, 40))
              ; raise Fail "ppExpression: bad match")
   and ppMatch (m, cases) =
      ppAppPair ("CS", ppExpression m, ppList (List.map ppCase cases))
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
         then SOME (ppAppPair
                      ("Rec", ppType ty, ppList (List.map ppExpression l)))
      else NONE

   fun ppDefinition (s, t, m) =
      let
         fun ppName c = if PP.isSExp() then c else "val " ^ s ^ "_def = " ^ c
      in
         case t of
           Term.Abs _ =>
             let
                val (v, b) = Term.destAbs t
             in
                case m of
                   SOME (script, mm) =>
                    ppAppQuintuple
                       (ppName "tDef", ppQ s, ppExpression v, ppExpression b,
                        ppExpression mm,
                        if script = "" then ppS "NO_TAC" else ppFile script)
                 | NONE =>
                    ppAppTriple
                       (ppName "Def", ppQ s, ppExpression v, ppExpression b)
             end
         | _ => ppAppPair (ppName "Def0", ppQ s, ppExpression t)
      end

   fun ppDefinitions conv =
      List.mapPartial (Option.compose (ppDefinition, conv))
         (Consts.listDefinitions ())

end (* HolPP *)

(* ------------------------------------------------------------------------
   Export L3 specifications to HOL4
   ------------------------------------------------------------------------ *)

signature HolExport =
sig
   val export : string -> unit
   val spec : string * string -> unit
end

structure HolExport :> HolExport =
struct

local
   val bigrecords = ref true
   val monadic_export = ref false
   val sig_docs = ref true
   val underflow_before = ref false
   val simp = ref true
in
   fun useBigRecords () = !bigrecords
   fun isMonadicExport () = !monadic_export
   fun underflowBefore () = !underflow_before
   fun printSigDocs () = !sig_docs
   fun performSimplification () = !simp
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
              "sigdocs" => (check s andalso (sig_docs := b; true))
            | "bigrecords" => (check s andalso  (bigrecords := b; true))
            | "monadic" => (check s andalso (monadic_export := b; true))
            | "simp" => (check s andalso (simp := b; true))
            | "underflowbefore" =>
                 (check s andalso (underflow_before := b; true))
            | "" => true
            | _ => false
         end
       fun loop [] = raise Fail "process_destination: empty list"
         | loop (l as (h :: t)) = if process1 h then loop t
                                  else String.concatWith " " (List.rev l)
     in
       bigrecords := true
     ; monadic_export := false
     ; sig_docs := true
     ; simp := true
     ; underflow_before := false
     ; OS.Path.splitDirFile (loop l)
     end
end

local
   fun noFreeVars tm =
      List.null (List.filter (not o Lib.equal "_" o fst) (Term.freeVars tm))
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
      if isMonadicExport ()
         then noFreeVars tm
      else case Term.findTerm monadTerm tm of
             SOME t => (print "\n"
                        ; Lib.pp (PolyML.prettyRepresentation (t, 10))
                        ; false)
           | NONE => true
   fun popt c b a = print (if b then a else c)
   val popt0 = popt ""
   fun sConv t =
     (Convert.simpConv (performSimplification ()) (isMonadicExport ()) o
      Convert.boolMatchConv o Matches.boolifyMatches) t
in
   fun HOLconv () =
      let
         val width = 44
         val (mutable, s) = Monad.init ()
         val sty = Type.mkConstType s
         val mdfy = Monadify.monadifyDefn (mutable, sty)
         val dmdfy = Monadify.deMonadifyDefn sty
         fun lift name ty measure_ismonadic m =
            SOME (case (measure_ismonadic, Type.isMapTy ty) of
                     (false, false) =>
                        raise Fail
                           ("0-arg function is monadic but \
                            \measure is not: " ^ name)
                   | (false, true) =>
                       let
                          val (a, t) = Term.destAbs m
                          val x = Term.Var ("x", Term.primTypeOf a ** sty)
                       in
                          Term.mkAbs
                            (x,
                             Term.mkMatch
                               (x,
                                [(Term.mkPair
                                    (a, Term.Var ("_", sty)), t)]))
                       end
                   | (true, false) =>
                       let
                          val t = dmdfy false m
                          val s = Term.Var ("s", sty)
                       in
                          Term.mkAbs (s, Term.mkFst (Term.mkApply (t, s)))
                       end
                   | (true, true) =>
                       let
                          val (a, t) = Term.destAbs m
                          val t = dmdfy false t
                          val s = Term.Var ("s", sty)
                          val x = Term.Var ("x", Term.primTypeOf a ** sty)
                       in
                          Term.mkAbs
                            (x,
                             Term.mkMatch
                                (x,
                                 [(Term.mkPair (a, s),
                                   Term.mkFst (Term.mkApply (t, s)))]))
                       end)
         fun transform (name, def, recursive, measure) =
            let
               val ty = Term.primTypeOf def
               val (mm, measure_ismonadic) =
                  case measure of
                     SOME (_, f) =>
                        let
                           val mname = "measure'" ^ name
                           val mm = mdfy (mname, f, false)
                        in
                           (SOME mm, Monad.isMonadic (mname, Term.primTypeOf f))
                        end
                   | NONE => (NONE, false)
               val m = mdfy (name, def, recursive)
               val ismonadic = Monad.isMonadic (name, ty)
               val isfun = Monad.isFunctional (name, ty)
               val ispure = Monad.isPure (name, ty)
               val ismonadexport = isMonadicExport ()
               val monadexport =
                  not (recursive orelse ispure andalso ismonadic) andalso
                  ismonadexport
               val _ =
                 (ispure orelse ismonadic orelse
                  raise Fail ("Not monadic and not pure: " ^ name)) andalso
                 (not measure_ismonadic orelse ismonadic) orelse
                  raise Fail ("Measure is monadic when function is not: " ^
                              name)
               val mm = if Option.isSome mm andalso ismonadic andalso
                           not ispure
                          then lift name ty measure_ismonadic (Option.valOf mm)
                        else mm
               val m = if ismonadic
                         then ((if ismonadexport orelse ispure orelse
                                   not (performSimplification ())
                                  then Lib.I
                                else Convert.simplifyMonadicConv isfun) o
                               (if monadexport then Lib.I else dmdfy ispure)) m
                       else m
               val r = sConv m
               val m =
                 Option.map (fn m => (fst (Option.valOf measure), sConv m)) mm
            in
               Monad.removeMonadic (name, ty) (not (ispure andalso ismonadic))
             ; (r, m, isOkay r, isfun, ispure)
            end
      in
         fn {user, name, def, recursive, measure} : Consts.defn =>
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
                          val (r, m, ok, isfun, ispure) =
                            transform (name, def, recursive, measure)
                          val () = popt "bad" ok "ok"
                          val () = popt0 recursive "-rec"
                          val () = popt0 isfun
                                     (if ispure then "-pure" else "-fun")
                          val () = popt0 (Option.isSome m) "-measure"
                          val () = printn "."
                       in
                          SOME (name, r, m)
                       end
               else SOME (name, def, NONE) before printn "sys."
            end
      end
end

(*

val {user, name, def, recursive, measure} =
  List.nth (Consts.listDefinitions (), 4)

*)

fun HOLboiler "" = raise Fail "HOLboiler: empty name"
  | HOLboiler name =
   let
      val script = name ^ "Script"
      val lib = name ^ "Lib"
      val theory = name ^ "Theory"
      val date = Date.toString (Date.fromTimeLocal (Time.now ()))
      val s = if printSigDocs () then "1" else "0"
   in
     ([PP.ppS ("(* " ^ script ^ ".sml - generated by L3 - " ^ date ^ " *)\n"),
       PP.ppS "open HolKernel boolLib bossLib Import\n\n",
       PP.ppS ("val () = Import.start " ^ quote name ^ "\n\n")] @
      (if isMonadicExport () then [PP.ppS ("open monadsyntax\n\n")] else []) @
      (if underflowBefore ()
         then [PP.ppS ("val () = ieee_underflow_before := true\n\n")]
       else []) @
      (if useBigRecords () then []
       else [PP.ppS ("val Record = NoBigRecord\n\n")]),
      [PP.ppS ("\nval () = Import.finish " ^ s)],
      [PP.ppS ("(* " ^ lib ^ " - generated by L3 - " ^ date ^ " *)\n"),
       PP.ppS ("structure " ^ lib ^ " :> " ^ lib ^ " =\n"),
       PP.ppS ("struct\n"),
       PP.ppS "open HolKernel boolLib bossLib\n",
       PP.ppS ("open utilsLib " ^ theory ^ "\n"),
       PP.ppS ("val () = (numLib.prefer_num (); wordsLib.prefer_word ())\n"),
       PP.ppS ("fun " ^ name ^ "_compset thms =\n"),
       PP.ppS ("   utilsLib.theory_compset (thms, " ^ name ^
               "Theory.inventory)\n"),
       PP.ppS ("end")],
      [PP.ppS ("(* " ^ lib ^ " - generated by L3 - " ^ date ^ " *)\n"),
       PP.ppS ("signature " ^ lib ^ " =\n"),
       PP.ppS ("sig\n"),
       PP.ppS ("   val " ^ name ^
               "_compset: Thm.thm list -> computeLib.compset\n"),
       PP.ppS ("end")],
      script, lib)
   end

fun out dir s e =
   PP.savePP
      (OS.Path.joinDirFile
          {dir = dir, file = OS.Path.joinBaseExt {base = s, ext = SOME e}})

fun export s =
   let
      val {file = name, dir} = process_destination s
      val out = out dir
      val () = Monad.stateName (name ^ "_state")
      val cnv = HOLconv ()
      val defs = HolPP.ppDefinitions cnv
      val q =
        [PP.ppS ("val qTy = CTy " ^ quote (Monad.state ())),
         PP.ppS "fun qVar v = Term.mk_var (v, ParseDatatype.pretypeToType qTy)"]
        handle Option.Option => []
      val l = Lib.mapSeparate I [PP.ppS ";\n"] (HolPP.ppTypeDefs () @ q @ defs)
      val (head, foot, sml, sml_sig, script, lib) = HOLboiler name
   in
      out script "sml" (head @ l @ foot)
      ; out lib "sml" sml
      ; out lib "sig" sml_sig
      ; printn "Done."
   end

fun spec (specfiles, name) =
   let
      val b = Parser.raiseErrors NONE
      val _ = Parser.raiseErrors (SOME true)
      val err = (Runtime.LoadF specfiles; NONE) handle exc => SOME exc
   in
      case err of
         SOME exc => (print "Export aborted.\n"; raise exc)
       | NONE => (PP.sExpExport false; export name)
      ; General.ignore (Parser.raiseErrors (SOME b))
   end

end (* structure HolExport *)
