signature LIVENESS =
sig
  structure IGraph : GRAPH
  datatype igraph = IGRAPH of {graph:IGraph.graph,
                               tnode:Temp.temp -> IGraph.node,
                               gtemp:IGraph.node -> Temp.temp,
                               moves:(IGraph.node * IGraph.node) list}

  val interferenceGraph : Flow.flowgraph -> igraph * (Flow.Graph.node -> Temp.temp list)

  val show : TextIO.outstream * igraph -> unit
end

structure Liveness : LIVENESS =
struct
  structure IGraph = Graph
  structure G = IGraph

  type liveSet = unit Temp.Table.table * Temp.temp list
  type liveMap = liveSet Flow.Graph.Table.table


  datatype igraph = IGRAPH of {graph:G.graph,
                               tnode:Temp.temp -> G.node,
                               gtemp:G.node -> Temp.temp,
                               moves:(G.node * G.node) list}

  fun interferenceGraph(Flow.FGRAPH{control, def, use, ismove}) =
    let
      fun tnode(temp) =
        ()
      fun gnode(node) =
        ()
    in
      ()
    end

  fun show(out, igraph) =
    ()

end
