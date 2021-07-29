structure Runtime :> Runtime =
struct

local
   val second = Time.fromReal 1.0
   val minute = Time.fromReal 60.0
   val year0 = Date.year (Date.fromTimeUniv Time.zeroTime)
   fun to_str i u = if i = 0 then "" else Int.toString i ^ u
in
   fun timeToString t =
      if Time.< (t, second)
         then Time.fmt 5 t ^ "s"
      else if Time.< (t, minute)
         then Time.fmt 1 t ^ "s"
      else let
              val d = Date.fromTimeUniv t
              val years = Date.year d - year0
              val days = Date.yearDay d
              val hours = Date.hour d
              val minutes = Date.minute d
           in
              if years + days + hours = 0 andalso minutes < 10 then
                 to_str minutes "m" ^ Date.fmt "%Ss" d
              else to_str years "y" ^ to_str days "d" ^ to_str hours "h" ^
                   Date.fmt "%Mm%Ss" d
           end
end

fun start_time () = Timer.startCPUTimer ()

fun end_time timer =
   let
      val {sys, usr} = Timer.checkCPUTimer timer
      val gc = Timer.checkGCTime timer
   in
      TextIO.output (TextIO.stdOut,
           "runtime: " ^ timeToString usr ^ ",\
       \    gctime: " ^ timeToString gc ^ ", \
       \    systime: " ^ timeToString sys ^ ".\n");
      TextIO.flushOut TextIO.stdOut
   end

fun time f x =
   let
      val timer = start_time ()
      val y = f x handle e => (end_time timer; raise e)
   in
      end_time timer; y
   end

end
