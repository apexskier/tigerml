CM.make "sources.cm";
let val args = CommandLine.arguments()
in
  Parse.parse hd args;
  OS.Process.exit(OS.Process.success)
end
