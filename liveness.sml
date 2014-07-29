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
  structure A = Assem

  structure IGraph = Graph
  structure G = IGraph
  structure GT = G.Table

  structure T = Temp
  structure TT = T.Table

  structure FG = Flow.Graph
  structure FGT = FG.Table

  type liveSet = unit TT.table * T.temp list
  type liveMap = liveSet FGT.table
  structure tempSet = ListSetFn
    (struct
      type ord_key = T.temp
      val compare = Int.compare
    end)

  datatype igraph = IGRAPH of {graph:G.graph,
                               tnode:T.temp -> G.node,
                               gtemp:G.node -> T.temp,
                               moves:(G.node * G.node) list}

  fun interferenceGraph(Flow.FGRAPH{control, def, use, ismove}) =
    let
      fun makeSet(list:T.temp list) =
        tempSet.addList(tempSet.empty, list)
      fun makeLiveSet(liveTemps : T.temp list) =
        let
          fun genLiveSet(tempTbl, temps, nil) = (tempTbl, temps)
            | genLiveSet(tempTbl, temps, temp::temptail) =
                let
                  val tempTbl' = TT.enter(tempTbl, temp, ())
                  val temps' = temp::temps
                in
                  genLiveSet(tempTbl', temps', temptail)
                end
        in
          genLiveSet(TT.empty, nil, liveTemps)
        end

      fun valOf(tbl, object) =
        case TT.look(tbl, object)
          of SOME n => n
           | NONE => ErrorMsg.impossible "table lookup failed"

      fun lookSet(tbl, node) =
        let
          val (g, n) = node
        in
          makeSet(valOf(tbl, n))
        end

      val fgNodes = G.nodes(control)

      val outLiveMap = FGT.empty
      val inLiveMap = FGT.empty

      val graphMoves = nil:(G.node * G.node) list
      val iGraph = G.newGraph()

      fun genINodes(h::t:FG.node list, (nodesMap, tempsMap)) =
        (case FGT.look(def, h)
          of SOME vars =>
            let fun enter(var:T.temp, (nodesMap', tempsMap')) =
              case TT.look(nodesMap', var)
                of SOME(node) => (nodesMap', tempsMap')
                 | NONE =>
                  let
                    val node = G.newNode(iGraph)
                  in
                    (TT.enter(nodesMap', var, node),
                     GT.enter(tempsMap', node, var))
                  end
            in
              foldl enter (nodesMap, tempsMap) vars
            end
           | NONE => (nodesMap, tempsMap))
        | genINodes(nil, (nodesMap, tempsMap)) = (nodesMap, tempsMap)

      val (iGraphNodes, iGraphTemps) = genINodes(fgNodes, (TT.empty, GT.empty))

      fun tnode(t:T.temp):G.node =
        case GT.look(iGraphNodes, (iGraph, t))
          of SOME node => node
           | NONE => ErrorMsg.impossible ("node not found for temp '" ^ T.makeString t ^ "'")

      fun gtemp(n:G.node):T.temp =
        case GT.look(iGraphTemps, n)
          of SOME temp => temp
           | NONE => ErrorMsg.impossible ("node '" ^ G.nodename n ^ "' not found")

      (* Use a dynamic programming approach here to save what's already been calculated *)
      fun calcIn(node:G.node):tempSet.set =
        (print ("in calcin for node " ^ G.nodename node ^ "\n");
        case FGT.look(inLiveMap, node)
          of SOME(temps) => temps
           | NONE =>
            let
              val temps = if G.nodename node = "n0" then lookSet(use, node)
                          else tempSet.union(lookSet(use, node),
                                        tempSet.difference(calcOut(node),
                                                           lookSet(def, node)))
            in
              FGT.enter(inLiveMap, node, temps);
              temps
            end)
      and calcOut(node:G.node):tempSet.set =
        let
          fun unionIn(node':G.node, outs:tempSet.set) =
            (print ("in calcout.unionIn for node " ^ G.nodename node ^ " looking at node' " ^ G.nodename node' ^ "\n");
            tempSet.union(outs, calcIn(node')))
        in
          print ("in calcout for node " ^ G.nodename node ^ "\n");
          case FGT.look(outLiveMap, node)
            of SOME(temps) => temps
             | NONE =>
              let
                val temps = foldl unionIn tempSet.empty (G.succ(node))
              in
                FGT.enter(outLiveMap, node, temps);
                temps
              end
        end

      fun outList(node:G.node):T.temp list =
        tempSet.listItems(calcOut(node))

      fun genIGraph(h::t, moves) =
            let
              val _ = print ("entered genIGraph for node " ^ G.nodename h ^ "\n")
              val outs = outList(h)
              val (g, n) = h
              val _ = print ("processing node " ^ G.nodename h ^ "\n")
            in
              if case TT.look(ismove, n)
                   of SOME(b) => b
                    | NONE => ErrorMsg.impossible "node ismove not found" then
                let
                  val a = tnode(
                    case TT.look(def, n)
                      of SOME(t) => if length t > 1 then ErrorMsg.impossible "more than one destination in move" else hd t
                       | NONE => ErrorMsg.impossible "destination not found in move CF node")
                  val c = tnode(
                    case TT.look(use, n)
                      of SOME(t) => if length t > 1 then ErrorMsg.impossible "more than one source in move" else hd t
                       | NONE => ErrorMsg.impossible "source not found in move CF node")
                  fun addEdge(b) =
                    let val b' = tnode(b)
                    in
                      if G.eq(b', c) then ()
                      else G.mk_edge{from=a, to=b'}
                    end
                in
                  app addEdge outs;
                  genIGraph(t, (a, c) :: moves)
                end
              else
                (case TT.look(def, n)
                  of SOME vars =>
                    let
                      fun mkedges(var:T.temp) =
                        let
                          val varNode = tnode(var)
                          fun mkedges'(out:T.temp) =
                            let
                              val outNode = tnode(out)
                            in
                              G.mk_edge{from=varNode, to=outNode}
                            end
                        in
                          app mkedges' outs
                        end
                    in
                      app mkedges vars
                    end
                   | NONE => ();
              genIGraph(t, moves))
            end
        | genIGraph(nil, moves) = moves

      val moves = genIGraph(rev fgNodes, nil)
      val _ = print "igraph generated\n"

      fun gTemp(node:G.node):T.temp =
        case GT.look(iGraphTemps, node)
          of SOME(t) => t
           | NONE => ErrorMsg.impossible ("temp -> node '" ^ G.nodename node ^ "' not found")

    in
      (IGRAPH{graph=iGraph,
              tnode=tnode,
              gtemp=gTemp,
              moves=moves}, outList)
    end

  and show(out, IGRAPH{graph, tnode, gtemp, moves}) =
    let
      val _ = print "printing igraph\n"
      val nodeList = G.nodes graph
      val nodeStrings = (fn n => (G.nodename n ^ "-" ^ T.makeString(gtemp n)))
      fun nodeStr(n) =
        nodeStrings n ^ " --> " ^ (String.concatWith ", " (map nodeStrings (G.adj(n))))
    in
      TextIO.output(out, String.concatWith "\n" (map nodeStr nodeList) ^ "\n")
    end

end
