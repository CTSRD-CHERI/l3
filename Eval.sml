PolyML.use "Base.sml";

(* -------------------------------------------------------------------------
   Stack
   ------------------------------------------------------------------------- *)

signature Stack =
sig
   type 'a stack
   val buildStack: (string * 'a) list -> 'a stack
   val empty: 'a stack
   val lookup: string -> 'a stack -> 'a option
   val modify: string * 'a -> 'a stack -> 'a stack
   val pop: string -> 'a stack -> 'a stack
   val push: (string * 'a) -> 'a stack -> 'a stack
end

structure Stack :> Stack =
struct
   type 'a stack = (string * 'a) list

   val empty = [] : 'a stack

   fun push v (l: 'a stack) = v :: l : 'a stack

   fun pop v (l: 'a stack) =
      case Lib.pluck (equal v o fst) l of
        SOME (_, r) => r
      | NONE => raise Fail ("pop: " ^ v)

   fun lookup v (l: 'a stack) = Option.map snd (List.find (equal v o fst) l)

   fun modify (v, x) =
      let
         fun iter a =
            fn [] => raise Fail ("modify: " ^ v)
             | (h as (n, _))::t =>
                 if v = n
                    then List.revAppend (a, (n, x) :: t)
                 else iter (h::a) t
      in
         iter []
      end

   fun buildStack l = List.foldl (uncurry push) empty l
end

(* -------------------------------------------------------------------------
   Eval (L3 interpreter)
   ------------------------------------------------------------------------- *)

signature Eval =
sig
   type term_stack = Term.term Stack.stack

   exception Eval of term_stack * Term.term
   exception Except of string * Term.term option

   val eval: term_stack -> Term.term -> term_stack * Term.term
   val evalBoolTerm: Term.term -> bool option
   val evalNatTerm: Term.term -> int option
   val initialize: Type.ty -> Term.term
end

(* -- *)

structure Eval :> Eval =
struct

type term_stack = Term.term Stack.stack

exception Eval of term_stack * Term.term
exception Except of string * Term.term option

fun error v m = raise Except (m, v)
fun error0 s = error NONE s

fun lift_error e t =
   error (SOME t)
      (case e of
          Domain => "Domain"
        | Subscript => "Subscript"
        | Option => "Option"
        | Div => "Div"
        | Fail m => "Fail: " ^ m
        | _ => raise e)

val destEnum = fst o Term.destEnumLit

fun toEnum s n =
   let
      val msg = "[" ^ Int.toString n ^ "] /-> " ^ s
   in
      case Types.sizeEnum s of
         SOME m => if n < m then Term.Lit (Term.Enum (n, s)) else error0 msg
       | NONE => error0 msg
   end

fun wordSize tm = Option.valOf (Type.bitsSize (Term.typeOf tm))
                  handle Option => raise Fail "wordSize"

fun initialize (ty as (bty, c)) =
   case bty of
      Type.ConstType c =>
          (case Types.lookupConst c of
             SOME { def = Types.Record l, ... } =>
               Term.Comb ("!" ^ c, ty, List.map (initialize o snd) l)
           | SOME { def = Types.Typedef ty2, ... } => initialize ty2
           | SOME _ => Term.unknown ty
           | NONE => raise Fail "initialize")
    | Type.Arrow _ =>
          let
             val (ty1, ty2) = Type.domrng ty
          in
             Term.absList [("x", ty1)] (initialize ty2)
          end
    | Type.Prod tys =>
          let
             val (ty1, ty2) = Type.fstsnd ty
          in
             Term.mkPair (initialize ty1, initialize ty2)
          end
    | _ => Term.unknown ty

fun matchCase x tm =
   let
      val (p, b) = Term.destCase tm
   in
      case Term.tryMatch p x of
         SOME (m, []) => SOME (Term.inst m b)
       | _ => NONE
   end

fun setInsert (tm1, tm2) =
   case tm2 of
      Term.Lit (Term.Other ("{}", ty)) => Term.Comb ("{..}", ty, [tm1])
    | Term.Comb ("{..}", ty, l as _::_) =>
         if Lib.memEq (Lib.uncurry Term.equalTm) tm1 l
            then tm2
         else Term.Comb ("{..}", ty, tm1 :: l)
    | _ => raise Fail "setInsert"

fun setCardinality tm =
   case tm of
      Term.Lit (Term.Other ("{}", _)) => Term.mkNatLit 0
    | Term.Comb ("{..}", _, l as _::_) =>
        Term.mkNatLit (IntInf.fromInt (List.length l))
    | _ => raise Fail "setCardinality"

fun setUnion (tm1, tm2) =
   case (tm1, tm2) of
      (_, Term.Lit (Term.Other ("{}", _))) => tm1
    | (Term.Lit (Term.Other ("{}", _)), _) => tm2
    | (Term.Comb ("{..}", _, l1 as _::_),
       Term.Comb ("{..}", ty, l2 as _::_)) => Term.mkTermSet (l1 @ l2)
    | _ => raise Fail "setUnion"

local
   val memTm = Lib.memEq (Lib.uncurry Term.equalTm)
in
   fun setIsSubset (tm1, tm2) =
      case (tm1, tm2) of
         (Term.Lit (Term.Other ("{}", _)), _) => Term.mkBoolLit true
       | (_, Term.Lit (Term.Other ("{}", _))) => Term.mkBoolLit false
       | (Term.Comb ("{..}", _, l1 as _::_),
          Term.Comb ("{..}", ty, l2 as _::_)) =>
             Term.mkBoolLit (List.all (fn x => memTm x l2) l1)
       | _ => raise Fail "setIsSubset"
   fun setIntersect (tm1, tm2) =
      case (tm1, tm2) of
         (_, Term.Lit (Term.Other ("{}", _))) => tm2
       | (Term.Lit (Term.Other ("{}", _)), _) => tm1
       | (Term.Comb ("{..}", _, l1 as _::_),
          Term.Comb ("{..}", ty, l2 as _::_)) =>
          let
             val l3 = List.filter (fn x => memTm x l2) l1
          in
             if List.null l3
                then Term.Lit (Term.Other ("{}", ty))
             else Term.Comb ("{..}", ty, l3)
          end
       | _ => raise Fail "setIntersect"
   fun setDifference (tm1, tm2) =
      case (tm1, tm2) of
         (_, Term.Lit (Term.Other ("{}", _))) => tm1
       | (Term.Lit (Term.Other ("{}", _)), _) => tm1
       | (Term.Comb ("{..}", _, l1 as _::_),
          Term.Comb ("{..}", ty, l2 as _::_)) =>
          let
             val l3 = List.filter (fn x => not (memTm x l2)) l1
          in
             if List.null l3
                then Term.Lit (Term.Other ("{}", ty))
             else Term.Comb ("{..}", ty, l3)
          end
       | _ => raise Fail "setDifference"
end

fun listConcat (tm1, tm2) =
   let
      fun iter (Term.Lit (Term.Other ("Nil", _))) = tm2
        | iter (Term.Comb ("Cons", ty1, [Term.Comb (",", ty2, [h, t])])) =
             Term.Comb ("Cons", ty1, [Term.Comb (",", ty2, [h, iter t])])
        | iter _ = raise Fail "listConcat"
   in
      iter tm1
   end

fun listRemove (l1, l2) =
   List.filter (fn x => not (Lib.memEq (Lib.uncurry Term.equalTm) x l2)) l1

fun listRemoveExcept (l1, l2) =
   List.filter (fn x => Lib.memEq (Lib.uncurry Term.equalTm) x l2) l1

fun isRegisterCons (f, ty) =
   case fst (Types.expand ty) of
     Type.ConstType c =>
        (case Types.lookupConst c of
           SOME { def = Types.Record _, ... } => f = c
         | _ => false)
   | _ => false

fun containsUnknown tm =
   Option.isSome
     (Term.findTerm (fn Term.Lit (Term.Other ("UNKNOWN", _)) => true
                      | _ => false) tm)

val natOptionTy = Type.optionTy Type.natTy
val intOptionTy = Type.optionTy Type.intTy

val mkNatOption =
   fn SOME n => Term.Comb ("Some", natOptionTy, [Term.mkNatLit n])
    | NONE => Term.Lit (Term.Other ("None", natOptionTy))

val mkIntOption =
   fn SOME n => Term.Comb ("Some", intOptionTy, [Term.mkIntLit n])
    | NONE => Term.Lit (Term.Other ("None", intOptionTy))

fun mkFlags ({DivideByZero = a, InvalidOp = b, Overflow = c, Precision = d,
              Underflow = e}, r) =
  Term.mkPair
    (Term.Comb (Tag.mkRecord "ieee_flags", Type.ieee_flagsTy,
                List.map Term.mkBoolLit [a, b, c, d, e]),
     Term.mkBitsLit r)

val single = fn [a] => a | _ => raise Domain
fun pair (f, g) = fn [a, b] => (f a, g b) | _ => raise Domain
fun triple (f, g, h) = fn [a, b, c] => (f a, g b, h c) | _ => raise Domain
fun quad (f, g, h, i) =
   fn [a, b, c, d] => (f a, g b, h c, i d) | _ => raise Domain

open Term

fun fp_triple l =
   let
      val (a, b) = destPair (single l)
      val (b, c) = destPair b
   in
      (destRounding a, (destBitsLit b, destBitsLit c))
   end
   handle Domain => (printn (PolyML.makestring l); raise Domain)

fun fp_quad l =
   let
      val (a, b) = destPair (single l)
      val (b, c) = destPair b
      val (c, d) = destPair c
   in
      (destRounding a, (destBitsLit b, (destBitsLit c, destBitsLit d)))
   end
   handle Domain => (printn (PolyML.makestring l); raise Domain)

fun cbv (ty, s, f) =
   fn env =>
      let
         fun iter (env, a) =
            fn [] =>
               (env,
                let
                   val a = List.rev a
                in
                   f a : Term.term
                   handle e => lift_error e (Term.Comb (s, ty, a))
                end)
             | h::t =>
                let
                   val (env', r) = eval env (h: Term.term)
                in
                   iter (env', r::a) t
                end
      in
         iter (env, [])
      end
and liftuNat (s, f) = cbv (Type.natTy, s, mkNumLit o f o destNumLit o single)
and liftuInt (s, f) = cbv (Type.intTy, s, mkIntLit o f o destIntLit o single)
and liftuBits ty (s, f) = cbv (ty, s, mkBitsLit o f o destBitsLit o single)
and liftbBits1 ty (s, f) =
   cbv (ty, s, mkBitsLit o f o (destBitsLit ## destBitsLit) o destPair o single)
and liftbBits ty (s, f) =
   cbv (ty, s, mkBitsLit o f o pair (destBitsLit, destBitsLit))
and liftbNat (s, f) =
   cbv (Type.natTy, s, mkNumLit o f o pair (destNumLit, destNumLit))
and liftbInt (s, f) =
   cbv (Type.intTy, s, mkIntLit o f o pair (destIntLit, destIntLit))
and liftbBitstring (s, f) =
   cbv (Type.bitstringTy, s,
        mkBitstringLit o f o pair (destBitstringLit, destBitstringLit))
and liftNatRel (s, f) =
   cbv (Type.boolTy, s, mkBoolLit o f o pair (destNumLit, destNumLit))
and liftIntRel (s, f) =
   cbv (Type.boolTy, s, mkBoolLit o f o pair (destIntLit, destIntLit))
and liftBitsRel (s, f) =
   cbv (Type.boolTy, s, mkBoolLit o f o pair (destBitsLit, destBitsLit))
and liftOrdering (s, f1, f2, f3) env a =
   case Term.dTypeOf (hd a) of
      Type.Other "nat" => liftNatRel (s, f1) env a
    | Type.Other "int" => liftIntRel (s, f2) env a
    | Type.FixedBits _ => liftBitsRel (s, f3) env a
    | _ => raise Eval (env, Comb (s, Type.boolTy, a))
and liftsBits ty (s, f1, f2) env a =
   case Term.dTypeOf (hd (tl a)) of
      Type.Other "nat" =>
         cbv (ty, s, mkBitsLit o f1 o pair (destBitsLit, destNumLit)) env a
    | Type.FixedBits _ => liftbBits ty (s, f2) env a
    | _ => raise Eval (env, Comb (s, ty, a))
and liftCharRel (s, f) =
   cbv (Type.boolTy, s, mkBoolLit o f o destCharLit o single)
and eval (env: term_stack) =
   fn Lit (Other ("FP32_PosInf", _)) => (env, mkBitsLit FP32.posInf)
    | Lit (Other ("FP32_NegInf", _)) => (env, mkBitsLit FP32.negInf)
    | Lit (Other ("FP32_PosZero", _)) => (env, mkBitsLit FP32.posZero)
    | Lit (Other ("FP32_NegZero", _)) => (env, mkBitsLit FP32.negZero)
    | Lit (Other ("FP32_PosMax", _)) => (env, mkBitsLit FP32.posMax)
    | Lit (Other ("FP32_NegMax", _)) => (env, mkBitsLit FP32.negMax)
    | Lit (Other ("FP32_PosMin", _)) => (env, mkBitsLit FP32.posMin)
    | Lit (Other ("FP32_NegMin", _)) => (env, mkBitsLit FP32.negMin)
    | Lit (Other ("FP32_qNan", _)) => (env, mkBitsLit FP32.qNan)
    | Lit (Other ("FP32_sNan", _)) => (env, mkBitsLit FP32.sNan)
    | Lit (Other ("FP64_PosInf", _)) => (env, mkBitsLit FP64.posInf)
    | Lit (Other ("FP64_NegInf", _)) => (env, mkBitsLit FP64.negInf)
    | Lit (Other ("FP64_PosZero", _)) => (env, mkBitsLit FP64.posZero)
    | Lit (Other ("FP64_NegZero", _)) => (env, mkBitsLit FP64.negZero)
    | Lit (Other ("FP64_PosMax", _)) => (env, mkBitsLit FP64.posMax)
    | Lit (Other ("FP64_NegMax", _)) => (env, mkBitsLit FP64.negMax)
    | Lit (Other ("FP64_PosMin", _)) => (env, mkBitsLit FP64.posMin)
    | Lit (Other ("FP64_NegMin", _)) => (env, mkBitsLit FP64.negMin)
    | Lit (Other ("FP64_qNan", _)) => (env, mkBitsLit FP64.qNan)
    | Lit (Other ("FP64_sNan", _)) => (env, mkBitsLit FP64.sNan)
    | t as Lit _ => (env, t)
    | t as Abs _ => (env, t)
    | t as BVar _ => (env, t)
    | Var (v, _) =>
       (case Stack.lookup v env of
           SOME v => (env, v)
         | _ => error0 ("Undeclared: " ^ v))
    | Comb ("<-", _, [Var (v, _), a]) =>
        let
           val (env', res) = eval env a
        in
           (Stack.modify (v, res) env', unitTm)
        end
    | Comb ("var =", _, [Var (v, _), a, b]) =>
        let
           val (env1, res) = eval env a
           val env2 = Stack.push (v, res) env1
           val (env3, res2) = eval env2 b
        in
           (Stack.pop v env3, res2)
        end
    | t as Comb ("i-t-e", ty, [b, l, r]) =>
       (case eval env b of
           (env', Lit (Bool true)) => eval env' l
         | (env', Lit (Bool false)) => eval env' r
         | (env', v) => raise Eval (env', Comb ("i-t-e", ty, [v, l, r])))
    | Comb ("and", ty, [l, r]) =>
       (case eval env l of
           f as (_, Lit (Bool false)) => f
         | (env', Lit (Bool true)) => eval env' r
         | (env', v) => raise Eval (env', Comb ("and", ty, [v, r])))
    | Comb ("or", ty, [l, r]) =>
       (case eval env l of
           t as (_, Lit (Bool true)) => t
         | (env', Lit (Bool false)) => eval env' r
         | (env', v) => raise Eval (env', Comb ("or", ty, [v, r])))
    | Comb (",", ty, a as [_, _]) =>
        cbv (ty, ",", fn [l, r] => mkPair (l, r) | _ => raise Domain) env a
    | Comb ("Fst", ty, a as [_]) =>
        cbv (ty, "fst", fst o destPair o single) env a
    | Comb ("Snd", ty, a as [_]) =>
        cbv (ty, "snd", snd o destPair o single) env a
    | Comb ("not", _, a as [_]) =>
        cbv (Type.boolTy, "not", mkBoolLit o not o destBoolLit o single) env a
    | Comb ("ToLower", _, a as [_]) =>
        cbv (Type.stringTy, "ToLower",
             mkStringLit o String.map Char.toLower o destStringLit o single)
            env a
    | Comb ("ToUpper", _, a as [_]) =>
        cbv (Type.stringTy, "ToUpper",
             mkStringLit o String.map Char.toUpper o destStringLit o single)
            env a
    | Comb ("FromBinString", _, a as [_]) =>
        cbv (natOptionTy, "FromBinString",
             mkNatOption o Nat.fromBinString o destStringLit o single) env a
    | Comb ("FromDecString", _, a as [_]) =>
        cbv (natOptionTy, "FromString",
             mkNatOption o Nat.fromString o destStringLit o single) env a
    | Comb ("FromHexString", _, a as [_]) =>
        cbv (natOptionTy, "FromHexString",
             mkNatOption o Nat.fromHexString o destStringLit o single) env a
    | Comb (s as "IsAlpha", _, a as [_]) =>
         liftCharRel (s, Char.isAlpha) env a
    | Comb (s as "IsAlphaNum", _, a as [_]) =>
         liftCharRel (s, Char.isAlphaNum) env a
    | Comb (s as "IsDigit", _, a as [_]) =>
         liftCharRel (s, Char.isDigit) env a
    | Comb (s as "IsHexDigit", _, a as [_]) =>
         liftCharRel (s, Char.isHexDigit) env a
    | Comb (s as "IsLower", _, a as [_]) =>
         liftCharRel (s, Char.isLower) env a
    | Comb (s as "IsSpace", _, a as [_]) =>
         liftCharRel (s, Char.isSpace) env a
    | Comb (s as "IsUpper", _, a as [_]) =>
         liftCharRel (s, Char.isUpper) env a
    | Comb ("splitl", _, a as [_, _]) =>
        cbv (Type.stringTy ** Type.stringTy, "split",
             fn [f, x] =>
               let
                  val s = Term.destStringLit x
                  fun P c =
                     snd (eval Stack.empty (mkApply (f, Term.mkCharLit c)))
                  val (l, r) = L3.splitl (fn c => Term.destBoolLit (P c), s)
               in
                  Term.mkPair (Term.mkStringLit l, Term.mkStringLit r)
               end
              | _ => raise Domain) env a
    | Comb ("splitr", _, a as [_, _]) =>
        cbv (Type.stringTy ** Type.stringTy, "split",
             fn [f, x] =>
               let
                  val s = Term.destStringLit x
                  fun P c =
                     snd (eval Stack.empty (mkApply (f, Term.mkCharLit c)))
                  val (l, r) = L3.splitr (fn c => Term.destBoolLit (P c), s)
               in
                  Term.mkPair (Term.mkStringLit l, Term.mkStringLit r)
               end
              | _ => raise Domain) env a
    | Comb ("fields", _, a as [_, _]) =>
        cbv (Type.listTy Type.stringTy, "tokens",
             fn [f, x] =>
               let
                  val s = Term.destStringLit x
                  fun P c =
                     snd (eval Stack.empty (mkApply (f, Term.mkCharLit c)))
                  val r = String.fields (fn c => Term.destBoolLit (P c)) s
               in
                  Term.mkList (mkStringLit, Type.listTy Type.stringTy) r
               end
              | _ => raise Domain) env a
    | Comb ("tokens", _, a as [_, _]) =>
        cbv (Type.listTy Type.stringTy, "tokens",
             fn [f, x] =>
               let
                  val s = Term.destStringLit x
                  fun P c =
                     snd (eval Stack.empty (mkApply (f, Term.mkCharLit c)))
                  val r = String.tokens (fn c => Term.destBoolLit (P c)) s
               in
                  Term.mkList (mkStringLit, Type.listTy Type.stringTy) r
               end
              | _ => raise Domain) env a
    | t as Comb ("==", _, a as [_, _]) =>
        cbv (Type.boolTy, "==",
             fn [l, r] => mkBoolLit (Term.equalTm l r) | _ => raise Domain)
            env a
    | t as Comb ("<", _, a as [_, _]) =>
        liftOrdering ("<", Nat.<, IntInf.<, BitsN.<) env a
    | t as Comb ("<=", _, a as [_, _]) =>
        liftOrdering ("<=", Nat.<=, IntInf.<=, BitsN.<=) env a
    | t as Comb (">", _, a as [_, _]) =>
        liftOrdering (">", Nat.>, IntInf.>, BitsN.>) env a
    | t as Comb (">=", _, a as [_, _]) =>
        liftOrdering (">=", Nat.>=, IntInf.>=, BitsN.>=) env a
    | Comb ("<+", _, a as [_, _])  => liftBitsRel ("<+", BitsN.<+) env a
    | Comb ("<=+", _, a as [_, _]) => liftBitsRel ("<=+", BitsN.<=+) env a
    | Comb (">+", _, a as [_, _])  => liftBitsRel (">+", BitsN.>+) env a
    | Comb (">=+", _, a as [_, _]) => liftBitsRel (">=+", BitsN.>=+) env a
    | t as Comb ("Log2", ty, a as [_]) =>
       (case Types.dest ty of
           Type.Other "nat" => liftuNat ("Log2", Nat.log2) env a
         | Type.FixedBits _ => liftuBits ty ("Log2", BitsN.log2) env a
         | _ => raise Eval (env, t))
    | t as Comb ("-", ty, a as [_]) =>
       (case Types.dest ty of
           Type.Other "int" => liftuInt ("-", IntInf.~) env a
         | Type.FixedBits _ => liftuBits ty ("-", BitsN.neg) env a
         | _ => raise Eval (env, t))
    | t as Comb ("-", ty, a as [_, _]) =>
       (case Types.dest ty of
           Type.Other "nat" => liftbNat ("-", Nat.-) env a
         | Type.Other "int" => liftbInt ("-", IntInf.-) env a
         | Type.FixedBits _ => liftbBits ty ("-", BitsN.-) env a
         | _ => raise Eval (env, t))
    | t as Comb ("+", ty, a as [_, _]) =>
        (case Types.dest ty of
           Type.Other "nat" => liftbNat ("+", Nat.+) env a
         | Type.Other "int" => liftbInt ("+", IntInf.+) env a
         | Type.Other "bitstring" => liftbBitstring ("+", Bitstring.+) env a
         | Type.FixedBits _ => liftbBits ty ("+", BitsN.+) env a
         | _ => raise Eval (env, t))
    | t as Comb ("*", ty, a as [_, _]) =>
       (case Types.dest ty of
           Type.Other "nat" => liftbNat ("*", Nat.*) env a
         | Type.Other "int" => liftbInt ("*", IntInf.*) env a
         | Type.FixedBits _ => liftbBits ty ("*", BitsN.*) env a
         | _ => raise Eval (env, t))
    | t as Comb ("**", ty, a as [_, _]) =>
       (case Types.dest ty of
           Type.Other "nat" => liftbNat ("**", Nat.pow) env a
         | Type.Other "int" =>
             cbv (ty, "**",
                  mkIntLit o IntInf.pow o
                  pair (destIntLit, IntInf.toInt o destNatLit)) env a
         | _ => raise Eval (env, t))
    | t as Comb ("quot", ty, a as [_, _]) =>
       (case Types.dest ty of
           Type.Other "int" => liftbInt ("quot", IntInf.quot) env a
         | Type.FixedBits _ => liftbBits ty ("quot", BitsN.quot) env a
         | _ => raise Eval (env, t))
    | t as Comb ("rem", ty, a as [_, _]) =>
       (case Types.dest ty of
           Type.Other "int" => liftbInt ("rem", IntInf.rem) env a
         | Type.FixedBits _ => liftbBits ty ("rem", BitsN.rem) env a
         | _ => raise Eval (env, t))
    | t as Comb ("QuotRem", ty, a as [_]) =>
        cbv (ty, "QuotRem",
             mkPair o (mkIntLit ## mkIntLit) o IntInf.quotRem o
             (destIntLit ## destIntLit) o destPair o single) env a
    | t as Comb ("div", ty, a as [_, _]) =>
       (case Types.dest ty of
           Type.Other "nat" => liftbNat ("div", Nat.div) env a
         | Type.Other "int" => liftbInt ("div", IntInf.div) env a
         | Type.FixedBits _ => liftbBits ty ("div", BitsN.div) env a
         | _ => raise Eval (env, t))
    | t as Comb ("mod", ty, a as [_, _]) =>
       (case Types.dest ty of
           Type.Other "nat" => liftbNat ("mod", Nat.mod) env a
         | Type.Other "int" => liftbInt ("mod", IntInf.mod) env a
         | Type.FixedBits _ => liftbBits ty ("mod", BitsN.mod) env a
         | _ => raise Eval (env, t))
    | t as Comb ("sdiv", ty, a as [_, _]) =>
       (case Types.dest ty of
           Type.FixedBits _ => liftbBits ty ("sdiv", BitsN.sdiv) env a
         | _ => raise Eval (env, t))
    | t as Comb ("smod", ty, a as [_, _]) =>
       (case Types.dest ty of
           Type.FixedBits _ => liftbBits ty ("smod", BitsN.smod) env a
         | _ => raise Eval (env, t))
    | t as Comb ("Abs", ty, a as [_]) =>
       (case Types.dest ty of
           Type.Other "int" => liftuInt ("Abs", IntInf.abs) env a
         | Type.FixedBits _ => liftuBits ty ("Abs", BitsN.abs) env a
         | _ => raise Eval (env, t))
    | t as Comb ("Min", ty, a as [_]) =>
       (case Types.dest ty of
           Type.Other "nat" =>
              cbv (ty, "Min",
                   mkNumLit o Nat.min o (destNumLit ## destNumLit) o
                   destPair o single) env a
         | Type.Other "int" =>
              cbv (ty, "Min",
                   mkIntLit o IntInf.min o (destIntLit ## destIntLit) o
                   destPair o single) env a
         | Type.FixedBits _ => liftbBits1 ty ("Min", BitsN.min) env a
         | _ => raise Eval (env, t))
    | t as Comb ("Max", ty, a as [_]) =>
       (case Types.dest ty of
           Type.Other "nat" =>
              cbv (ty, "Max",
                   mkNumLit o Nat.max o (destNumLit ## destNumLit) o
                   destPair o single) env a
         | Type.Other "int" =>
              cbv (ty, "Max",
                   mkIntLit o IntInf.max o (destIntLit ## destIntLit) o
                   destPair o single) env a
         | Type.FixedBits _ => liftbBits1 ty ("Max", BitsN.max) env a
         | _ => raise Eval (env, t))
    | t as Comb ("SignedMin", ty, [a]) =>
        liftbBits1 ty ("SignedMin", BitsN.smin) env [a]
    | t as Comb ("SignedMax", ty, [a]) =>
        liftbBits1 ty ("SignedMax", BitsN.smax) env [a]
    | t as Comb ("Msb", _, a as [_]) =>
        cbv (Type.boolTy, "Msb",
             mkBoolLit o BitsN.msb o destBitsLit o single) env a
    | t as Comb ("Reverse", ty, a as [_]) =>
       (case Types.dest ty of
           Type.FixedBits _ => liftuBits ty ("Reverse", BitsN.reverse) env a
         | Type.Other "string" =>
              cbv (ty, "Reverse",
                   mkStringLit o L3.revString o destStringLit o single) env a
         | Type.Other "bitstring" =>
              cbv (ty, "Reverse",
                   mkBitstringLit o List.rev o destBitstringLit o single) env a
         | Type.Other "list" =>
              cbv (ty, "Reverse",
                   mkList (I, ty) o List.rev o destList o single) env a
         | _ => raise Eval (env, t))
    | t as Comb ("Take", ty, a as [_]) =>
       (case Types.dest ty of
           Type.Other "string" =>
              cbv (ty, "Take",
                   mkStringLit o L3.takeString o
                   (destNumLit ## destStringLit) o
                   destPair o single) env a
         | Type.Other "bitstring" =>
              cbv (ty, "Take",
                   mkBitstringLit o List.take o L3.swap o
                   (IntInf.toInt o destNumLit ## destBitstringLit) o destPair o
                   single) env a
         | Type.Other "list" =>
              cbv (ty, "Take",
                   mkList (I, ty) o List.take o L3.swap o
                   (IntInf.toInt o destNumLit ## destList) o destPair o single)
                   env a
         | _ => raise Eval (env, t))
    | t as Comb ("Drop", ty, a as [_]) =>
       (case Types.dest ty of
           Type.Other "string" =>
              cbv (ty, "Drop",
                   mkStringLit o L3.dropString o (destNumLit ## destStringLit) o
                   destPair o single) env a
         | Type.Other "bitstring" =>
              cbv (ty, "Drop",
                   mkBitstringLit o List.drop o L3.swap o
                   (IntInf.toInt o destNumLit ## destBitstringLit) o destPair o
                   single) env a
         | Type.Other "list" =>
              cbv (ty, "Drop",
                   mkList (I, ty) o List.drop o L3.swap o
                   (IntInf.toInt o destNumLit ## destList) o destPair o single)
                   env a
         | _ => raise Eval (env, t))
    | t as Comb ("Update", ty, a as [_]) =>
       (case Types.dest ty of
             Type.Other "string" =>
              cbv (ty, "Update",
                   mkStringLit o L3.stringUpdate o
                   (Term.destCharLit ## (destNumLit ## destStringLit)) o
                   destTriple o single) env a
         | Type.Other "bitstring" =>
              cbv (ty, "Update",
                   mkBitstringLit o L3.listUpdate o
                   (Term.destBoolLit ## (destNumLit ## destBitstringLit)) o
                   destTriple o single) env a
         | Type.Other "list" =>
              cbv (ty, "Update",
                   mkList (I, ty) o L3.listUpdate o
                   (I ## (destNumLit ## destList)) o destTriple o single) env a
         | _ => raise Eval (env, t))
    | t as Comb ("Element", ty, a as [_]) =>
       (case Types.dest (Type.listTy ty) of
           Type.Other "string" =>
              cbv (ty, "Element",
                   mkCharLit o String.sub o L3.swap o
                   (IntInf.toInt o destNumLit ## destStringLit) o destPair o
                   single) env a
         | Type.Other "bitstring" =>
              cbv (ty, "Element",
                   mkBoolLit o List.nth o L3.swap o
                   (IntInf.toInt o destNumLit ## destBitstringLit) o destPair o
                   single) env a
         | Type.Other "list" =>
              cbv (ty, "Element",
                   List.nth o L3.swap o
                   (IntInf.toInt o destNumLit ## destList) o destPair o single)
                   env a
         | _ => raise Eval (env, t))
    | t as Comb ("Remove", ty, a as [_]) =>
       (case Types.dest ty of
           Type.Other "string" =>
              cbv (ty, "Remove",
                   mkStringLit o L3.removeString o
                   (destStringLit ## destStringLit) o destPair o single) env a
         | Type.Other "bitstring" =>
              cbv (ty, "Remove",
                   mkBitstringLit o L3.remove o
                   (destBitstringLit ## destBitstringLit) o
                   destPair o single) env a
         | Type.Other "list" =>
              cbv (ty, "Remove",
                   mkList (I, ty) o listRemove o (destList ## destList) o
                   destPair o single) env a
         | _ => raise Eval (env, t))
    | t as Comb ("RemoveExcept", ty, a as [_]) =>
       (case Types.dest ty of
           Type.Other "string" =>
              cbv (ty, "RemoveExcept",
                   mkStringLit o L3.removeExceptString o
                   (destStringLit ## destStringLit) o destPair o single) env a
         | Type.Other "bitstring" =>
              cbv (ty, "RemoveExcept",
                   mkBitstringLit o Set.intersect o
                   (destBitstringLit ## destBitstringLit) o
                   destPair o single) env a
         | Type.Other "list" =>
              cbv (ty, "RemoveExcept",
                   mkList (I, ty) o listRemoveExcept o
                   (destList ## destList) o destPair o single) env a
         | _ => raise Eval (env, t))
    | t as Comb ("RemoveDuplicates", ty, a as [_]) =>
       (case Types.dest ty of
           Type.Other "string" =>
              cbv (ty, "RemoveDuplicates",
                   mkStringLit o L3.removeDuplicatesString o
                   destStringLit o single) env a
         | Type.Other "bitstring" =>
              cbv (ty, "RemoveDuplicates",
                   mkBitstringLit o Set.mk o destBitstringLit o single) env a
         | Type.Other "list" =>
              cbv (ty, "RemoveDuplicates",
                   mkList (I, ty) o Lib.mkSetEq (Lib.uncurry Term.equalTm) o
                   destList o single) env a
         | _ => raise Eval (env, t))
    | t as Comb ("IsMember", _, a as [_]) =>
        cbv (Type.boolTy, "IsMember",
             mkBoolLit o
             (fn (x, l) => Option.isSome (List.find (Term.equalTm x) l)) o
             (I ## destList) o destPair o single) env a
    | t as Comb ("IndexOf", ty, a as [_]) =>
        cbv (ty, "IndexOf",
             mkNatOption o
             (L3.revLookup Term.equalTm) o (I ## destList) o destPair o single)
            env a
    | t as Comb ("~", ty, a as [_]) => liftuBits ty ("~", BitsN.~) env a
    | Comb ("&&", ty, a as [_, _]) =>
        (case Types.dest ty of
           Type.Other "bitstring" => liftbBitstring ("&&", Bitstring.&&) env a
         | _ => liftbBits ty ("&&", BitsN.&&) env a)
    | Comb ("||", ty, a as [_, _]) =>
        (case Types.dest ty of
           Type.Other "bitstring" => liftbBitstring ("||", Bitstring.||) env a
         | _ => liftbBits ty ("||", BitsN.||) env a)
    | Comb ("??", ty, a as [_, _]) =>
        (case Types.dest ty of
           Type.Other "bitstring" => liftbBitstring ("??", Bitstring.??) env a
         | _ => liftbBits ty ("??", BitsN.??) env a)
    | t as Comb ("<<", ty, a as [_, _]) =>
       (case Types.dest ty of
           Type.Other "bitstring" =>
              cbv (ty, "<<",
                   mkBitstringLit o Bitstring.<< o
                   pair (destBitstringLit, destNumLit)) env a
         | _ => liftsBits ty ("<<", BitsN.<<, BitsN.<<^) env a)
    | Comb (">>", ty, a as [_, _]) =>
        liftsBits ty (">>", BitsN.>>, BitsN.>>^) env a
    | Comb (">>+", ty, a as [_, _]) =>
       (case Types.dest ty of
           Type.Other "bitstring" =>
              cbv (ty, ">>+",
                   mkBitstringLit o Bitstring.>>+ o
                   pair (destBitstringLit, destNumLit)) env a
         | _ => liftsBits ty (">>+", BitsN.>>+, BitsN.>>+^) env a)
    | Comb ("#>>", ty, a as [_, _]) =>
       (case Types.dest ty of
           Type.Other "bitstring" =>
              cbv (ty, "#>>",
                   mkBitstringLit o Bitstring.#>> o
                   pair (destBitstringLit, destNumLit)) env a
         | _ => liftsBits ty ("#>>", BitsN.#>>, BitsN.#>>^) env a)
    | Comb ("#<<", ty, a as [_, _]) =>
        liftsBits ty ("#<<", BitsN.#<<, BitsN.#<<^) env a
    | t as Comb ("^", ty, a as [_, _]) =>
       (case Types.dest ty of
           Type.Other "bitstring" =>
              cbv (ty, "^",
                   mkBitstringLit o Bitstring.replicate o
                   pair (destBitstringLit, destNumLit)) env a
         | Type.FixedBits i =>
              cbv (ty, "^",
                   mkBitsLit o BitsN.resize_replicate i o
                   pair (destBitsLit, destNumLit)) env a
         | _ => raise Eval (env, t))
    | t as Comb ("Size", _, a as [_]) =>
        cbv (Type.natTy, "Size", mkNumLit o BitsN.size o destBitsLit o single)
            env a
    | t as Comb ("<.>", _, a as [l, _]) =>
       (case Term.dTypeOf l of
           Type.Other "bitstring" =>
              cbv (Type.boolTy, "<.>",
                   mkBoolLit o Bitstring.bit o
                   pair (destBitstringLit, destNumLit)) env a
         | Type.FixedBits _ =>
              cbv (Type.boolTy, "<.>",
                    mkBoolLit o BitsN.bit o
                    pair (destBitsLit, destNumLit)) env a
         | _ => raise Eval (env, t))
    | t as Comb ("<..>", ty, a as [_, _, _]) =>
       (case Types.dest ty of
           Type.Other "bitstring" =>
              cbv (ty, "<..>",
                   mkBitstringLit o
                   (fn (h,l,a) => Bitstring.bits (h,l) a) o
                   triple (destNumLit, destNumLit, destBitstringLit)) env a
         | Type.FixedBits s =>
              cbv (ty, "<..>",
                   mkBitsLit o  BitsN.zeroExtend (IntInf.fromInt s) o
                   (fn (h,l,a) => BitsN.bits (h,l) a) o
                   triple (destNumLit, destNumLit, destBitsLit)) env a
         | _ => raise Eval (env, t))
    | t as Comb ("ZeroExtend", ty, [a]) =>
       (case (Types.dest ty, Term.dTypeOf a) of
           (Type.FixedBits s, Type.FixedBits _) =>
                liftuBits ty
                   ("ZeroExtend", BitsN.zeroExtend (Nat.fromNativeInt s)) env
                    [a]
         | _ => raise Eval (env, t))
    | t as Comb ("SignExtend", ty, [a]) =>
       (case (Types.dest ty, Term.dTypeOf a) of
           (Type.FixedBits s, Type.FixedBits _) =>
                liftuBits ty
                   ("SignExtend", BitsN.signExtend (Nat.fromNativeInt s)) env
                    [a]
         | _ => raise Eval (env, t))
    | t as Comb ("bit-field-insert", ty, a as [_, _, _, b]) =>
       (case (Types.dest ty, Term.dTypeOf b) of
           (Type.Other "bitstring", Type.Other "bitstring") =>
              cbv (ty, "bit-field-insert",
                   mkBitstringLit o
                   (fn (h,l,a,b) => Bitstring.bitFieldInsert (h,l) (a,b)) o
                   quad (destNumLit, destNumLit, destBitstringLit,
                         destBitstringLit)) env a
         | (Type.FixedBits _, Type.FixedBits _) =>
              cbv (ty, "bit-field-insert",
                   mkBitsLit o
                   (fn (h,l,a,b) => BitsN.bitFieldInsert (h,l) (a,b)) o
                   quad (destNumLit, destNumLit, destBitsLit, destBitsLit))
                  env a
         | _ => raise Eval (env, t))
    | Comb ("FP32_FromInt", ty, a as [_]) =>
        cbv (ty, "FP32_FromInt",
             mkBitsLit o FP32.fromInt o (destRounding ## destIntLit) o
             destPair o single) env a
    | Comb ("FP32_RoundToIntegral", ty, a as [_]) =>
        cbv (ty, "FP32_RoundToIntegral",
             mkBitsLit o FP32.roundToIntegral o (destRounding ## destBitsLit) o
             destPair o single) env a
    | Comb ("FP32_ToInt", ty, a as [_]) =>
        cbv (intOptionTy, "FP32_ToInt",
             mkIntOption o FP32.toInt o (destRounding ## destBitsLit) o
             destPair o single) env a
    | Comb ("FP32_Sqrt_", ty, a as [_]) =>
        cbv (ty, "FP32_Sqrt_",
             mkFlags o FP32.sqrt o (destRounding ## destBitsLit) o
             destPair o single) env a
    | Comb ("FP32_Sqrt", ty, a as [_]) =>
        cbv (ty, "FP32_Sqrt",
             mkBitsLit o snd o FP32.sqrt o (destRounding ## destBitsLit) o
             destPair o single) env a
    | Comb ("FP32_Abs", ty, a as [_]) =>
        liftuBits ty ("FP32_Abs", FP32.abs) env a
    | Comb ("FP32_Neg", ty, a as [_]) =>
        liftuBits ty ("FP32_Neg", FP32.neg) env a
    | Comb ("FP32_Compare", ty, a as [_]) =>
        cbv (Type.boolTy, "FP32_Compare",
             mkCompare o FP32.compare o (destBitsLit ## destBitsLit) o
             destPair o single) env a
    | Comb ("FP32_Equal", ty, a as [_]) =>
        cbv (Type.boolTy, "FP32_Equal",
             mkBoolLit o FP32.equal o (destBitsLit ## destBitsLit) o
             destPair o single) env a
    | Comb ("FP32_GreaterThan", ty, a as [_]) =>
        cbv (Type.boolTy, "FP32_GreaterThan",
             mkBoolLit o FP32.greaterThan o (destBitsLit ## destBitsLit) o
             destPair o single) env a
    | Comb ("FP32_GreaterEqual", ty, a as [_]) =>
        cbv (Type.boolTy, "FP32_GreaterEqual",
             mkBoolLit o FP32.greaterEqual o (destBitsLit ## destBitsLit) o
             destPair o single) env a
    | Comb ("FP32_LessThan", ty, a as [_]) =>
        cbv (Type.boolTy, "FP32_LessThan",
             mkBoolLit o FP32.lessThan o (destBitsLit ## destBitsLit) o
             destPair o single) env a
    | Comb ("FP32_LessEqual", ty, a as [_]) =>
        cbv (Type.boolTy, "FP32_LessEqual",
             mkBoolLit o FP32.lessEqual o (destBitsLit ## destBitsLit) o
             destPair o single) env a
    | Comb ("FP32_IsIntegral", ty, a as [_]) =>
        cbv (Type.boolTy, "FP32_IsIntegral",
             mkBoolLit o FP32.isIntegral o destBitsLit o single) env a
    | Comb ("FP32_IsFinite", ty, a as [_]) =>
        cbv (Type.boolTy, "FP32_IsFinite",
             mkBoolLit o FP32.isFinite o destBitsLit o single) env a
    | Comb ("FP32_IsNan", ty, a as [_]) =>
        cbv (Type.boolTy, "FP32_IsNan",
             mkBoolLit o FP32.isNan o destBitsLit o single) env a
    | Comb ("FP32_IsNormal", ty, a as [_]) =>
        cbv (Type.boolTy, "FP32_IsNormal",
             mkBoolLit o FP32.isNormal o destBitsLit o single) env a
    | Comb ("FP32_IsSignallingNan", ty, a as [_]) =>
        cbv (Type.boolTy, "FP32_IsSignallingNan",
             mkBoolLit o FP32.isSignallingNan o destBitsLit o single) env a
    | Comb ("FP32_IsSubnormal", ty, a as [_]) =>
        cbv (Type.boolTy, "FP32_IsSubnormal",
             mkBoolLit o FP32.isSubnormal o destBitsLit o single) env a
    | Comb ("FP32_IsZero", ty, a as [_]) =>
        cbv (Type.boolTy, "FP32_IsZero",
             mkBoolLit o FP32.isZero o destBitsLit o single) env a
    | Comb ("FP32_Add_", ty, a as [_]) =>
        cbv (ty, "FP32_Add_", mkFlags o FP32.add o fp_triple) env a
    | Comb ("FP32_Sub_", ty, a as [_]) =>
        cbv (ty, "FP32_Sub_", mkFlags o FP32.sub o fp_triple) env a
    | Comb ("FP32_Mul_", ty, a as [_]) =>
        cbv (ty, "FP32_Mul_", mkFlags o FP32.mul o fp_triple) env a
    | Comb ("FP32_Div_", ty, a as [_]) =>
        cbv (ty, "FP32_Div_", mkFlags o FP32.div o fp_triple) env a
    | Comb ("FP32_MulAdd_", ty, a as [_]) =>
        cbv (ty, "FP32_MulAdd_", mkFlags o FP32.mul_add o fp_quad) env a
    | Comb ("FP32_MulSub_", ty, a as [_]) =>
        cbv (ty, "FP32_MulSub_", mkFlags o FP32.mul_sub o fp_quad) env a
    | Comb ("FP32_Add", ty, a as [_]) =>
        cbv (ty, "FP32_Add", mkBitsLit o snd o FP32.add o fp_triple) env a
    | Comb ("FP32_Sub", ty, a as [_]) =>
        cbv (ty, "FP32_Sub", mkBitsLit o snd o FP32.sub o fp_triple) env a
    | Comb ("FP32_Div", ty, a as [_]) =>
        cbv (ty, "FP32_Div", mkBitsLit o snd o FP32.div o fp_triple) env a
    | Comb ("FP32_Mul", ty, a as [_]) =>
        cbv (ty, "FP32_Mul", mkBitsLit o snd o FP32.mul o fp_triple) env a
    | Comb ("FP32_MulAdd", ty, a as [_]) =>
        cbv (ty, "FP32_MulAdd", mkBitsLit o snd o FP32.mul_add o fp_quad) env a
    | Comb ("FP32_MulSub", ty, a as [_]) =>
        cbv (ty, "FP32_MulSub", mkBitsLit o snd o FP32.mul_sub o fp_quad) env a
    | Comb ("FP32_ToFP64", ty, a as [_]) =>
        cbv (ty, "FP32_ToFP64", mkBitsLit o FPConvert.fp32_to_fp64 o
             destBitsLit o single) env a
    | Comb ("FP64_ToFP32", ty, a as [_]) =>
        cbv (ty, "FP64_ToFP32",
             mkBitsLit o FPConvert.fp64_to_fp32 o
             (destRounding ## destBitsLit) o destPair o single) env a
    | Comb ("FP64_ToFP32_", ty, a as [_]) =>
        cbv (ty, "FP64_ToFP32",
             mkFlags o FPConvert.fp64_to_fp32_with_flags o
             (destRounding ## destBitsLit) o destPair o single) env a
    | Comb ("FP64_FromInt", ty, a as [_]) =>
        cbv (ty, "FP64_FromInt",
             mkBitsLit o FP64.fromInt o (destRounding ## destIntLit) o
             destPair o single) env a
    | Comb ("FP64_RoundToIntegral", ty, a as [_]) =>
        cbv (ty, "FP64_RoundToIntegral",
             mkBitsLit o FP64.roundToIntegral o (destRounding ## destBitsLit) o
             destPair o single) env a
    | Comb ("FP64_ToInt", ty, a as [_]) =>
        cbv (intOptionTy, "FP64_ToInt",
             mkIntOption o FP64.toInt o (destRounding ## destBitsLit) o
             destPair o single) env a
    | Comb ("FP64_Sqrt_", ty, a as [_]) =>
        cbv (ty, "FP64_Sqrt_",
             mkFlags o FP64.sqrt o (destRounding ## destBitsLit) o
             destPair o single) env a
    | Comb ("FP64_Sqrt", ty, a as [_]) =>
        cbv (ty, "FP64_Sqrt",
             mkBitsLit o snd o FP64.sqrt o (destRounding ## destBitsLit) o
             destPair o single) env a
    | Comb ("FP64_Abs", ty, a as [_]) =>
        liftuBits ty ("FP64_Abs", FP64.abs) env a
    | Comb ("FP64_Neg", ty, a as [_]) =>
        liftuBits ty ("FP64_Neg", FP64.neg) env a
    | Comb ("FP64_Compare", ty, a as [_]) =>
        cbv (Type.boolTy, "FP64_Compare",
             mkCompare o FP64.compare o (destBitsLit ## destBitsLit) o
             destPair o single) env a
    | Comb ("FP64_Equal", ty, a as [_]) =>
        cbv (Type.boolTy, "FP64_Equal",
             mkBoolLit o FP64.equal o (destBitsLit ## destBitsLit) o
             destPair o single) env a
    | Comb ("FP64_GreaterThan", ty, a as [_]) =>
        cbv (Type.boolTy, "FP64_GreaterThan",
             mkBoolLit o FP64.greaterThan o (destBitsLit ## destBitsLit) o
             destPair o single) env a
    | Comb ("FP64_GreaterEqual", ty, a as [_]) =>
        cbv (Type.boolTy, "FP64_GreaterEqual",
             mkBoolLit o FP64.greaterEqual o (destBitsLit ## destBitsLit) o
             destPair o single) env a
    | Comb ("FP64_LessThan", ty, a as [_]) =>
        cbv (Type.boolTy, "FP64_LessThan",
             mkBoolLit o FP64.lessThan o (destBitsLit ## destBitsLit) o
             destPair o single) env a
    | Comb ("FP64_LessEqual", ty, a as [_]) =>
        cbv (Type.boolTy, "FP64_LessEqual",
             mkBoolLit o FP64.lessEqual o (destBitsLit ## destBitsLit) o
             destPair o single) env a
    | Comb ("FP64_IsIntegral", ty, a as [_]) =>
        cbv (Type.boolTy, "FP64_IsIntegral",
             mkBoolLit o FP64.isIntegral o destBitsLit o single) env a
    | Comb ("FP64_IsFinite", ty, a as [_]) =>
        cbv (Type.boolTy, "FP64_IsFinite",
             mkBoolLit o FP64.isFinite o destBitsLit o single) env a
    | Comb ("FP64_IsNan", ty, a as [_]) =>
        cbv (Type.boolTy, "FP64_IsNan",
             mkBoolLit o FP64.isNan o destBitsLit o single) env a
    | Comb ("FP64_IsNormal", ty, a as [_]) =>
        cbv (Type.boolTy, "FP64_IsNormal",
             mkBoolLit o FP64.isNormal o destBitsLit o single) env a
    | Comb ("FP64_IsSignallingNan", ty, a as [_]) =>
        cbv (Type.boolTy, "FP64_IsSignallingNan",
             mkBoolLit o FP64.isSignallingNan o destBitsLit o single) env a
    | Comb ("FP64_IsSubnormal", ty, a as [_]) =>
        cbv (Type.boolTy, "FP64_IsSubnormal",
             mkBoolLit o FP64.isSubnormal o destBitsLit o single) env a
    | Comb ("FP64_IsZero", ty, a as [_]) =>
        cbv (Type.boolTy, "FP64_IsSubnormal",
             mkBoolLit o FP64.isZero o destBitsLit o single) env a
    | Comb ("FP64_Add_", ty, a as [_]) =>
        cbv (ty, "FP64_Add_", mkFlags o FP64.add o fp_triple) env a
    | Comb ("FP64_Sub_", ty, a as [_]) =>
        cbv (ty, "FP64_Sub_", mkFlags o FP64.sub o fp_triple) env a
    | Comb ("FP64_Mul_", ty, a as [_]) =>
        cbv (ty, "FP64_Mul_", mkFlags o FP64.mul o fp_triple) env a
    | Comb ("FP64_Div_", ty, a as [_]) =>
        cbv (ty, "FP64_Div_", mkFlags o FP64.div o fp_triple) env a
    | Comb ("FP64_MulAdd_", ty, a as [_]) =>
        cbv (ty, "FP64_MulAdd_", mkFlags o FP64.mul_add o fp_quad) env a
    | Comb ("FP64_MulSub_", ty, a as [_]) =>
        cbv (ty, "FP64_MulSub_", mkFlags o FP64.mul_sub o fp_quad) env a
    | Comb ("FP64_Add", ty, a as [_]) =>
        cbv (ty, "FP64_Add", mkBitsLit o snd o FP64.add o fp_triple) env a
    | Comb ("FP64_Sub", ty, a as [_]) =>
        cbv (ty, "FP64_Sub", mkBitsLit o snd o FP64.sub o fp_triple) env a
    | Comb ("FP64_Mul", ty, a as [_]) =>
        cbv (ty, "FP64_Mul", mkBitsLit o snd o FP64.mul o fp_triple) env a
    | Comb ("FP64_Div", ty, a as [_]) =>
        cbv (ty, "FP64_Div", mkBitsLit o snd o FP64.div o fp_triple) env a
    | Comb ("FP64_MulAdd", ty, a as [_]) =>
        cbv (ty, "FP64_MulAdd", mkBitsLit o snd o FP64.mul_add o fp_quad) env a
    | Comb ("FP64_MulSub", ty, a as [_]) =>
        cbv (ty, "FP64_MulSub", mkBitsLit o snd o FP64.mul_sub o fp_quad) env a
    | t as Comb ("PadLeft", ty, a as [_]) =>
       (case Types.dest ty of
           Type.Other "string" =>
              cbv (ty, "PadLeft",
                   (fn a =>
                      let
                         val (v, nl) = Term.destPair a
                         val nl =
                           (destNatLit ## destStringLit) (Term.destPair nl)
                      in
                         mkStringLit (L3.padLeftString (destCharLit v, nl))
                      end) o single) env a
         | Type.Other "bitstring" =>
              cbv (ty, "PadLeft",
                   (fn a =>
                      let
                         val (v, nl) = Term.destPair a
                         val nl = (destNatLit ##
                                   (Bitstring.toList o destBitstringLit))
                                    (Term.destPair nl)
                      in
                         mkBitstringLit
                           (Bitstring.fromList (L3.padLeft (destBoolLit v, nl)))
                      end) o single) env a
         | _ => cbv (ty, "PadLeft",
                     (fn a =>
                        let
                           val (v, nl) = Term.destPair a
                           val nl = (destNatLit ## destList) (Term.destPair nl)
                        in
                           mkList (I, ty) (L3.padLeft (v, nl))
                        end) o single) env a)
    | t as Comb ("PadRight", ty, a as [_]) =>
       (case Types.dest ty of
           Type.Other "string" =>
              cbv (ty, "PadRight",
                   (fn a =>
                      let
                         val (v, nl) = Term.destPair a
                         val nl =
                           (destNatLit ## destStringLit) (Term.destPair nl)
                      in
                         mkStringLit (L3.padRightString (destCharLit v, nl))
                      end) o single) env a
         | Type.Other "bitstring" =>
              cbv (ty, "PadRight",
                   (fn a =>
                      let
                         val (v, nl) = Term.destPair a
                         val nl = (destNatLit ##
                                   (Bitstring.toList o destBitstringLit))
                                    (Term.destPair nl)
                      in
                         mkBitstringLit
                           (Bitstring.fromList
                              (L3.padRight (destBoolLit v, nl)))
                      end) o single) env a
         | _ => cbv (ty, "PadRight",
                     (fn a =>
                        let
                           val (v, nl) = Term.destPair a
                           val nl = (destNatLit ## destList) (Term.destPair nl)
                        in
                           mkList (I, ty) (L3.padRight (v, nl))
                        end) o single) env a)
    | t as Comb ("Concat", ty, a as [_]) =>
       (case Types.dest ty of
           Type.Other "string" =>
              cbv (ty, "Concat",
                   mkStringLit o String.concat o List.map destStringLit o
                   destList o single) env a
         | Type.Other "bitstring" =>
              cbv (ty, "Concat",
                   mkBitstringLit o List.concat o
                   List.map Term.destBitstringLit o
                   destList o single) env a
         | _ => cbv (ty, "Concat",
                     mkList (I, ty) o List.concat o List.map destList o
                     destList o single) env a)
    | t as Comb (":", ty, a as [l, r]) =>
       (case Types.dest ty of
           Type.Other "string" =>
             cbv (ty, ":",
                  mkStringLit o String.^ o pair (destStringLit, destStringLit))
                 env a
         | Type.Other "bitstring" => liftbBitstring (":", Bitstring.@@) env a
         | Type.Other "list" =>
             cbv (ty, ":", fn [x, y] => listConcat (x, y) | _ => raise Domain)
                 env a
         | Type.FixedBits s =>
             let
                val nl = wordSize l and nr = wordSize r
             in
                if nl + nr = s
                   then liftbBits ty (":", BitsN.@@) env a
                else (env, error0 ("Bad bits concatenation: " ^
                                   Int.toString nl ^ " + " ^
                                   Int.toString nr ^ " <> " ^
                                   Int.toString s))
             end
         | _ => raise Eval (env, t))
    (* contains location information *)
    | Comb ("[..]", ty, [Lit (Int _), a]) => eval env (Comb ("[..]", ty, [a]))
    | t as Comb ("[..]", ty, a as [x]) =>
        let
           fun lift (mk,dst) f = cbv (ty, "[..]", mk o f o dst o single) env a
        in
           case (Term.dTypeOf x, Types.dest ty) of
             (Type.Other "bool", Type.Other "bool") => eval env x
           | (Type.Other "char", Type.Other "char") => eval env x
           | (Type.Other "nat",  Type.Other "nat") => eval env x
           | (Type.Other "int",  Type.Other "int") => eval env x
           | (Type.Other "string", Type.Other "string") => eval env x
           | (Type.Other "bitstring", Type.Other "bitstring") => eval env x
           | (Type.Other "bool", Type.Other "char") =>
                lift (mkCharLit, destBoolLit) (fn b => if b then #"t" else #"f")
           | (Type.Other "bool", Type.Other "string") =>
                lift (mkStringLit, destBoolLit)
                     (fn b => if b then "true" else "false")
           | (Type.Other "bool", Type.Other "nat") =>
                lift (mkNumLit, destBoolLit)
                     (fn b => if b then Nat.one else Nat.zero)
           | (Type.Other "bool", Type.Other "int") =>
                lift (mkIntLit, destBoolLit)
                     (fn b => if b then 1 else 0)
           | (Type.Other "bool", Type.Other "bitstring") =>
                lift (mkBitstringLit, destBoolLit)
                     (fn b => (if b then Bitstring.one else Bitstring.zero)
                              Nat.one)
           | (Type.Other "bool", Type.FixedBits i) =>
                lift (mkBitsLit, destBoolLit)
                     (fn b => (if b then BitsN.one else BitsN.zero)
                              (Nat.fromNativeInt i))
           | (Type.Other "nat", Type.Other "bool") =>
                lift (mkBoolLit, destNumLit) (not o equal Nat.zero)
           | (Type.Other "nat", Type.Other "char") =>
                lift (mkCharLit, IntInf.toInt o destNumLit) Char.chr
           | (Type.Other "nat", Type.Other "string") =>
                lift (mkStringLit, destNumLit) Nat.toString
           | (Type.Other "nat", Type.Other "int") =>
                lift (mkIntLit, destNumLit) Nat.toInt
           | (Type.Other "nat", Type.Other "bitstring") =>
                lift (mkBitstringLit, destNumLit) Bitstring.fromNat
           | (Type.Other "nat", Type.Other s) =>
                if Types.isEnumerated s
                   then lift (toEnum s, IntInf.toInt o destNumLit) I
                else (env, error0 ("nat -> " ^ s))
           | (Type.Other "nat", Type.FixedBits i) =>
                lift (mkBitsLit, destNumLit)
                     (fn n => BitsN.fromNat (n, Nat.fromNativeInt i))
           | (Type.Other "int", Type.Other "bool") =>
                lift (mkBoolLit, destIntLit) (not o equal 0)
           | (Type.Other "int", Type.Other "char") =>
                lift (mkCharLit, IntInf.toInt o destIntLit) Char.chr
           | (Type.Other "int", Type.Other "string") =>
                lift (mkStringLit, destIntLit) IntInf.toString
           | (Type.Other "int", Type.Other "nat") =>
                lift (mkNumLit, destIntLit) Nat.fromInt
           | (Type.Other "int", Type.Other "bitstring") =>
                lift (mkBitstringLit, destIntLit) Bitstring.fromInt
           | (Type.Other "int", Type.Other s) =>
                if Types.isEnumerated s
                   then lift (toEnum s, IntInf.toInt o destIntLit) Lib.I
                else (env, error0 ("int -> " ^ s))
           | (Type.Other "int", Type.FixedBits i) =>
                lift (mkBitsLit, destIntLit)
                     (fn n => BitsN.fromInt (n, Nat.fromNativeInt i))
           | (Type.Other "bitstring", Type.Other "bool") =>
                lift (mkBoolLit, destBitstringLit)
                     (not o equal Nat.zero o Bitstring.toNat)
           | (Type.Other "bitstring", Type.Other "char") =>
                lift (mkCharLit, destBitstringLit)
                  (Char.chr o Nat.toNativeInt o Bitstring.toNat)
           | (Type.Other "bitstring", Type.Other "string") =>
                lift (mkStringLit, destBitstringLit) Bitstring.toBinString
           | (Type.Other "bitstring", Type.Other "nat") =>
                lift (mkNumLit, destBitstringLit) Bitstring.toNat
           | (Type.Other "bitstring", Type.Other "int") =>
                lift (mkIntLit, destBitstringLit) Bitstring.toInt
           | (Type.Other "bitstring", Type.Other s) =>
                if Types.isEnumerated s
                   then lift (toEnum s, destBitstringLit)
                             (Nat.toNativeInt o Bitstring.toNat)
                else (env, error0 ("bitstring -> " ^ s))
           | (Type.Other "bitstring", Type.FixedBits i) =>
                lift (mkBitsLit, destBitstringLit)
                     (fn n => BitsN.fromBitstring (n, Nat.fromNativeInt i))
           | (Type.Other "char", Type.Other "bool") =>
                lift (mkBoolLit, destCharLit) (equal #"t")
           | (Type.Other "char", Type.Other "string") =>
                lift (mkStringLit, destCharLit) String.str
           | (Type.Other "char", Type.Other "nat") =>
                lift (mkNumLit o IntInf.fromInt, destCharLit) Char.ord
           | (Type.Other "char", Type.Other "int") =>
                lift (mkIntLit o IntInf.fromInt, destCharLit) Char.ord
           | (Type.Other "char", Type.Other "bitstring") =>
                lift (mkBitstringLit, destCharLit)
                     (Bitstring.fromNat o IntInf.fromInt o Char.ord)
           | (Type.Other "char", Type.Other s) =>
                if Types.isEnumerated s
                   then lift (toEnum s, destCharLit) Char.ord
                else (env, error0 ("char -> " ^ s))
           | (Type.Other "char", Type.FixedBits i) =>
                lift (mkBitsLit, destCharLit)
                     (fn n => BitsN.fromNativeInt (Char.ord n, i))
           | (Type.Other "string", Type.Other "bool") =>
                lift (mkBoolLit, destStringLit)
                     (fn s => (case s of
                                 "true" => true
                               | "false" => false
                               | _ => raise Domain))
           | (Type.Other "string", Type.Other "char") =>
                lift (mkCharLit, destStringLit) L3.stringToChar
           | (Type.Other "string", Type.Other "int") =>
                lift (mkIntLit, destStringLit)
                     (Option.valOf o IntInf.fromString)
           | (Type.Other "string", Type.Other "nat") =>
                lift (mkNumLit, destStringLit)
                     (Option.valOf o Nat.fromString)
           | (Type.Other "string", Type.Other "bitstring") =>
                lift (mkBitstringLit, destStringLit)
                     (Option.valOf o Bitstring.fromBinString)
           | (Type.Other "string", Type.Other s) =>
                if Types.isEnumerated s
                   then lift (toEnum s, destStringLit)
                          (fn e =>
                              case Types.enum s e of
                                 SOME n => n
                               | NONE => error0 ("string -> " ^ s))
                else (env, error0 ("string -> " ^ s))
           | (Type.Other "string", Type.FixedBits i) =>
                lift (mkBitsLit, destStringLit)
                     (fn n => Option.valOf
                                 (BitsN.fromHexString (n, Nat.fromNativeInt i)))
           | (Type.Other s, Type.Other "char") =>
                if Types.isEnumerated s
                   then lift (mkCharLit, destEnum) Char.chr
                else (env, error0 (s ^ " -> char"))
           | (Type.Other s, Type.Other "string") =>
                if Types.isEnumerated s
                   then lift (mkStringLit, destEnum)
                             (fn n => Option.valOf (Types.revenum s n))
                else (env, error0 (s ^ " -> string"))
           | (Type.Other s, Type.Other "nat") =>
                if Types.isEnumerated s
                   then lift (mkNumLit, destEnum) IntInf.fromInt
                else (env, error0 (s ^ " -> nat"))
           | (Type.Other s, Type.Other "int") =>
                if Types.isEnumerated s
                   then lift (mkIntLit, destEnum) IntInf.fromInt
                else (env, error0 (s ^ " -> nat"))
           | (Type.Other s, Type.Other "bitstring") =>
                if Types.isEnumerated s
                   then lift (mkBitstringLit, IntInf.fromInt o destEnum)
                             Bitstring.fromNat
                else (env, error0 (s ^ " -> bitstring"))
           | (Type.Other s, Type.FixedBits i) =>
                if Types.isEnumerated s
                   then lift (mkBitsLit, destEnum)
                             (fn n => BitsN.fromNativeInt (n, i))
                else (env, error0 (s ^ " -> bits(" ^ Int.toString i ^ ")"))
           | (Type.Other s1, Type.Other s2) =>
                if Types.isEnumerated s1 andalso Types.isEnumerated s2
                   then lift (toEnum s2, destEnum) I
                else if s1 = s2
                   then eval env x
                else (env, error0 (s1 ^ " -> " ^ s2))
           | (Type.FixedBits i, Type.Other "bool") =>
                lift (mkBoolLit, destBitsLit)
                     (not o equal (BitsN.zero (Nat.fromNativeInt i)))
           | (Type.FixedBits i, Type.Other "char") =>
                lift (mkCharLit, destBitsLit)
                     (Char.chr o Nat.toNativeInt o BitsN.toNat)
           | (Type.FixedBits i, Type.Other "string") =>
                lift (mkStringLit, destBitsLit) BitsN.toHexString
           | (Type.FixedBits i, Type.Other "nat") =>
                lift (mkNumLit, destBitsLit) BitsN.toNat
           | (Type.FixedBits i, Type.Other "int") =>
                lift (mkIntLit, destBitsLit) BitsN.toInt
           | (Type.FixedBits i, Type.Other "bitstring") =>
                lift (mkBitstringLit, destBitsLit) BitsN.toBitstring
           | (Type.FixedBits i, Type.Other s) =>
                if Types.isEnumerated s
                   then lift (toEnum s, destBitsLit)
                             (Nat.toNativeInt o BitsN.toNat)
                else (env, error0 (" `" ^ Int.toString i ^ " -> " ^ s))
           | (Type.FixedBits i, Type.FixedBits j) =>
                lift (mkBitsLit, destBitsLit) (BitsN.resize j)
           | (x, y) => (env, error0 ("Bad cast: " ^ PolyML.makestring t))
        end
    | Comb (";", _, [a, b]) => eval (fst (eval env a)) b
    | Comb ("update-map", _, [m, i, e]) =>
        let
           val (env1, vm) = eval env m
           val (env2, vi) = eval env1 i
           val (env3, ve) = eval env2 e
           val ty1 = primTypeOf i
           val ty2 = primTypeOf e
           val v = ("v", ty1)
           val j = Var v
        in
           (env3,
            Term.absList [v]
               (Comb ("i-t-e", ty2, [Comb ("==", Type.boolTy, [j, vi]),
                                     ve, Term.apply vm j])))
        end
    (* contains location information *)
    | Comb ("match-loc", ty, Lit (Int _)::l) => eval env (Comb ("match", ty, l))
    | t as Comb ("match", _, m::l) =>
        let
           val (env1, v) = eval env m
           fun err s = (pp (PolyML.prettyRepresentation (v, 80))
                        ; (env1, error0 ("Match" ^ s)))
        in
           if 1 < List.length l andalso containsUnknown v
              then err ": contains unknown"
           else case findSome (matchCase v) l of
                   SOME tm => eval env1 tm
                 | NONE => err ""
        end
    | Comb ("{..}", ty, l as _::_) => cbv (ty, "{..}", mkTermSet) env l
    | Comb ("in", _, a as [_, _]) =>
        cbv (Type.boolTy, "in",
             fn [x, y] =>
                  mkBoolLit
                    (Lib.memEq (Lib.uncurry equalTm) x (destTermSet y))
              | _ => raise Domain) env a
    | Comb ("insert", ty, a as [_, _]) =>
        cbv (ty, "insert", fn [x, y] => setInsert (x, y) | _ => raise Domain)
            env a
    | Comb ("Cardinality", _, a as [_]) =>
        cbv (Type.natTy, "Cardinality", setCardinality o single) env a
    | Comb ("IsSubset", _, a as [_]) =>
        cbv (Type.boolTy, "IsSubset", setIsSubset o destPair o single) env a
    | Comb ("Union", ty, a as [_]) =>
        cbv (ty, "Union", setUnion o destPair o single) env a
    | Comb ("Intersect", ty, a as [_]) =>
        cbv (ty, "Intersect", setIntersect o destPair o single) env a
    | Comb ("Difference", ty, a as [_]) =>
        cbv (ty, "Difference", setDifference o destPair o single) env a
    | Comb ("for", _, [a, b, c]) =>
        let
           val (env1, s) = eval env a
           val (env2, f) = eval env b
           val (start, finish) =
              (Nat.toNativeInt (destNatLit s),
               Nat.toNativeInt (destNatLit f))
              handle Fail m =>
                raise Eval (env2, Comb ("for", Type.unitTy, [s, f, c]))
           val tms =
              if start <= finish
                 then List.tabulate
                         (finish + 1 - start,
                          fn i => mkApply
                                    (c, mkNatLit (IntInf.fromInt (start + i))))
              else List.tabulate
                      (start + 1 - finish,
                       fn i => mkApply
                                 (c, mkNatLit (IntInf.fromInt (start - i))))
        in
           cbv (Type.unitTy, "for", K unitTm) env2 tms
        end
    | Comb ("foreach", _, [a, b]) =>
        let
           val (env1, l) = eval env a
           val tms = List.map (fn t => mkApply (b, t)) (Term.destList l)
        in
           cbv (Type.unitTy, "foreach", K unitTm) env1 tms
        end
    | t as Comb ("abs-apply", ty, [a, b]) =>
        let
           val u = Types.match (primTypeOf a) (primTypeOf b --> ty)
           val (env1, f) = eval env (Term.termTypeSubst u a
                                     handle e => lift_error e a)
           val (env2, v) = eval env b
        in
           eval env2 (Term.apply f v handle Fail _ => raise Eval (env, t))
        end
    | t as Comb (f, ty, []) =>
        (case Consts.lookupConst f of
           Consts.Constructor _ => (env, t)
         | Consts.Accessor (tm, _, _) =>
              eval env (Term.matchType ty tm handle e => lift_error e t)
         | Consts.Definition (tm, _, _) =>
              eval env (Term.matchType ty tm handle e => lift_error e t)
         | Consts.Exception NONE => raise Except (f, NONE)
         | _ => raise Eval (env, t))
    | t as Comb (f, ty, [a]) =>
        let
           val (env', arg) = eval env a
        in
           case Consts.lookupConst f of
              Consts.Constructor _ =>
                (env', Term.normalizeCons (Term.Comb (f, ty, [arg])))
            | d as Consts.Destructor _ =>
                (case Consts.pickDestructor (Term.primTypeOf a --> ty) d of
                    SOME tm =>
                      eval env' (Term.mkMatchApply ty (tm, arg)
                                 handle e => lift_error e (Comb (f, ty, [arg])))
                  | NONE => raise Eval (env', t))
            | Consts.Accessor (rd, wr, _) =>
                let
                   val tm = if Types.equalTy (Term.primTypeOf rd)
                                             (Term.primTypeOf a --> ty)
                               then rd
                            else wr
                in
                   eval env' (Term.mkMatchApply ty (tm, arg)
                              handle e => lift_error e (Comb (f, ty, [arg])))
                end
            | Consts.Definition (tm, _, _) =>
                eval env' (Term.mkMatchApply ty (tm, arg)
                           handle e => lift_error e (Comb (f, ty, [arg])))
            | Consts.Exception (SOME _) => raise Except (f, SOME arg)
            | _ => raise Eval (env', t)
        end
    | t as Comb (f, ty, a) =>
        if Tag.isRecord f
           then cbv (ty, f, fn l => Comb (f, ty, l)) env a
        else raise Eval (env, t)

fun evalBoolTerm tm =
  SOME (Term.destBoolLit (snd (eval Stack.empty tm)))
  handle Except _ => NONE
       | Eval _ => NONE
       | Fail _ => NONE

fun evalNatTerm tm =
  SOME (Nat.toNativeInt (Term.destNatLit (snd (eval Stack.empty tm))))
  handle Except _ => NONE
       | Eval _ => NONE
       | Fail _ => NONE

end (* struct Eval *)
