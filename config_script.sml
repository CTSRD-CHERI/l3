val () =
  let
    val out = TextIO.openOut "PPInt.sml"
    val s = "structure PPInt = " ^
            (if PolyML.Compiler.compilerVersionNumber < 561
               then "Int"
             else "FixedInt")
  in
    TextIO.output (out, s)
  end
