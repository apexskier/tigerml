structure Flow =
struct
  structure Graph = Graph
  datatype flowgraph = FGRAPH of {control: Graph.graph,
                                  def: Temp.temp list Graph.Table.table,
                                  use: Temp.temp list Graph.Table.table,
                                  assem: Graph.node -> string,
                                  ismove: bool Graph.Table.table}


  fun show(out, FGRAPH{control, def, use, assem, ismove}) =
    let
      val nodeList = Graph.nodes control
      val nodeStrings = (fn n => (Graph.nodename n))
      fun nodeStr(n) =
        nodeStrings n ^ " --> " ^ (ListFormat.listToString Graph.nodename (Graph.adj(n))) ^ "\n\t\t\t" ^ assem n
    in
      TextIO.output(out, String.concatWith "" (map nodeStr (rev nodeList)) ^ "\n")
    end

  (* Note:  any "use" within the block is assumed to be BEFORE a "def"
  of the same variable.  If there is a def(x) followed by use(x)
  in the same block, do not mention the use in this data structure,
  mention only the def.

  More generally:
  If there are any nonzero number of defs, mention def(x).
  If there are any nonzero number of uses BEFORE THE FIRST DEF,
  mention use(x).

  For any node in the graph,
  Graph.Table.look(def,node) = SOME(def-list)
  Graph.Table.look(use,node) = SOME(use-list)
  *)
end
