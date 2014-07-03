(* Run this program with the name of a tiger file as an argument *)
CM.make "sources.cm";
let val args = CommandLine.arguments()
    val parsed = Parse.parse (hd args)
in
  PrintAbsyn.print(TextIO.stdOut, parsed);
  Semant.transProg(parsed)
end;
OS.Process.exit(OS.Process.success)
