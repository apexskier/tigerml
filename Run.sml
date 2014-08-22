structure Run =
struct
  fun main(prog_name, args) =
    (* Run this program with the name of a tiger file as an argument *)
    let
      val flags = ["--tree", "-t", "--canontree", "-ct", "--absyn", "-a", "--strings", "-s", "--cfgraph", "c", "--igraph", "-i", "--liveouts", "-l"]
      val absyn = List.exists (fn a => a = "--absyn" orelse a = "-a") args
      val tree = List.exists (fn a => a = "--tree" orelse a = "-t") args
      val canontree = List.exists (fn a => a = "--canontree" orelse a = "-ct") args
      val strings = List.exists (fn a => a = "--strings" orelse a = "-s") args
      val cfgraph = List.exists (fn a => a = "--cfgraph" orelse a = "-cfg") args
      val igraph = List.exists (fn a => a = "--igraph" orelse a = "-ig") args
      val liveout = List.exists (fn a => a = "--liveouts" orelse a = "-l") args
      val args' =
        List.filter (fn a => not(List.exists (fn f => a = f) flags)) args
      val input = List.last args'
    in
      Main.compile("test.tig", absyn, tree, canontree, strings, cfgraph, igraph, liveout);
      0
    end
      handle Fail msg =>
        (print ("compilation error: " ^ msg ^ "\n");
        1)
end
