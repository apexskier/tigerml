(* Run this program with the name of a tiger file as an argument *)
CM.make "sources.cm";
let val args = CommandLine.arguments()
in
  Parse.parse (hd args)
end;
OS.Process.exit(OS.Process.success)
