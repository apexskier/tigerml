(* Run this program with the name of a tiger file as an argument *)
CM.make "sources.cm";
print "\n## Lexical Analysis\n";
let val args = CommandLine.arguments()
    val parsed = Parse.parse (hd args)
in
  print "\n## Abstract Syntax Tree\n";
  PrintAbsyn.print(TextIO.stdOut, parsed);
  print "\n## Type checking\n";
  Semant.transProg(parsed);
  print "\n"
end;
OS.Process.exit(OS.Process.success)
