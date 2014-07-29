structure Amd64RegAlloc : REGALLOC =
struct
  structure Frame = Amd64Frame
  structure T = Temp
  structure TT = Temp.Table
  structure F = Frame

  type allocation = F.register TT.table

  fun alloc(instrs, frame) =
    let
      val _ = print "\n## Control flow graph\n"
      val (cfGraph as Flow.FGRAPH{control, def, use, ismove}, cfNodes) = MakeGraph.instrs2graph(instrs)
      val _ = Flow.show(TextIO.stdOut, cfGraph)

      val _ = print "\n## Interference graph\n"
      val (igraph as Liveness.IGRAPH{graph, tnode, gtemp, moves}, getOuts) = Liveness.interferenceGraph(cfGraph)
      val _ = Liveness.show(TextIO.stdOut, igraph)

      val (allocation, temps) = Amd64Color.color{interference=igraph,
                                                 initial=F.tempMap,
                                                 spillCost=(fn _ => 0),
                                                 registers=F.registers}
    in
      (instrs, allocation)
    end
end

