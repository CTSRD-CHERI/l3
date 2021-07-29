datatype 'a frag = QUOTE of string | ANTIQUOTE of 'a;

use "Export.sml";
use "HolExport.sml";
use "IsabelleExport.sml";
use "ILExport.sml";
use "SMLExport.sml";

structure Parse =
struct
   val Term = Runtime.evalQ
end;

fun main () = (TextIO.print "<< L3 >>\n"; PolyML.rootFunction ())
