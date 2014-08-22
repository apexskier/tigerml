structure Run =
struct
  fun main(prog_name, args) =
    (* Run this program with the name of a tiger file as an argument *)
    let
      val flags = ["--tree", "-t", "--canontree", "-ct", "--absyn", "-a", "--strings", "-s", "--cfgraph", "cfg", "--igraph", "-ig", "--liveouts", "-l", "--help", "-h"]
      val absyn = List.exists (fn a => a = "--absyn" orelse a = "-a") args
      val tree = List.exists (fn a => a = "--tree" orelse a = "-t") args
      val canontree = List.exists (fn a => a = "--canontree" orelse a = "-ct") args
      val strings = List.exists (fn a => a = "--strings" orelse a = "-s") args
      val cfgraph = List.exists (fn a => a = "--cfgraph" orelse a = "-cfg") args
      val igraph = List.exists (fn a => a = "--igraph" orelse a = "-ig") args
      val liveout = List.exists (fn a => a = "--liveouts" orelse a = "-l") args
      val help = List.exists (fn a => a = "--help" orelse a = "-h") args
      val args' =
        List.filter (fn a => not(List.exists (fn f => a = f) flags)) args
      val prog = hd args
      val args' =
        if length args' = 1 then
          []
        else tl args'
    in
      if help orelse length args' <> 1 then
        (print ("Usage: sml @SMLload " ^ prog ^ " [options] file\n");
        print "Options:\n";
        print "  --absyn, -a         Print abstract syntax tree representation.\n";
        print "  --tree, -t          Print pseudo-instruction tree form.\n";
        print "  --canontree, -ct    Print canonicalized tree form.\n";
        print "  --strings, -s       Print unique strings found in program.\n";
        print "  --cfgraph, -cfg     Print control flow graph.\n";
        print "  --igraph, -ig       Print interference graph.\n";
        print "  --liveouts, -l      Print liveness (out) information.\n";
        print "  --help, -h          Print this help message.\n";
        if not help then 1 else 0)
      else
        (Main.compile(List.last args', absyn, tree, canontree, strings, cfgraph, igraph, liveout);
        0)
    end
      handle Fail msg =>
        (print ("compilation error: " ^ msg ^ "\n");
        1)
end
