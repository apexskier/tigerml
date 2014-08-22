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

  fun format t =
    case T.Table.look(Amd64Frame.tempMap, t)
      of SOME s => "%" ^ s
       | NONE => T.makeString t

  datatype igraph = IGRAPH of {graph:G.graph,
                               tnode:T.temp -> G.node,
                               gtemp:G.node -> T.temp,
                               moves:(G.node * G.node) list}

  fun interferenceGraph(Flow.FGRAPH{control, def, assem, use, ismove}) =
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

      val fgNodes = G.nodes control

      val graphMoves = nil:(G.node * G.node) list
      val iGraph = G.newGraph()

      (* Create nodes in the interference graph for each variable defined in
        * the control flow graph. Save them in some lookup tables. *)
      fun genINodes(h::t:FG.node list, (nodesMap, tempsMap, cf2igMap)) =
            let
              fun processVarsFrom(table, (nodesMap', tempsMap', cf2igMap')) =
                case FGT.look(table, h)
                  of SOME vars =>
                    let
                      fun enter(var:T.temp, (nodesMap'', tempsMap'', cf2igMap'')) =
                        case TT.look(nodesMap'', var)
                          of SOME node => (nodesMap'', tempsMap'', cf2igMap'')
                           | NONE =>
                            let
                              val node = G.newNode iGraph
                            in
                              (TT.enter(nodesMap'', var, node),
                               GT.enter(tempsMap'', node, var),
                               FGT.enter(cf2igMap'', h, node))
                            end
                    in
                      foldl enter (nodesMap', tempsMap', cf2igMap') vars
                    end
                   | NONE => (nodesMap', tempsMap', cf2igMap')
            in
              genINodes(t, foldl processVarsFrom (nodesMap, tempsMap, cf2igMap) [def, use])
            end
        | genINodes(nil, (nodesMap, tempsMap, cf2igMap)) = (nodesMap, tempsMap, cf2igMap)

      val (iGraphNodes, iGraphTemps, cf2igMap) = genINodes(fgNodes, (TT.empty, GT.empty, FGT.empty))

      fun valOf(tbl, object) =
        case TT.look(tbl, object)
          of SOME n => n
           | NONE => ErrorMsg.impossible "table lookup failed"

      fun valOfFG(tbl, object) =
        case FGT.look(tbl, object)
          of SOME n => n
           | NONE => ErrorMsg.impossible "FG table lookup failed"

      fun lookSet(tbl, node) =
        let
          val (g, n) = node
        in
          makeSet(valOf(tbl, n))
        end

      fun convCFtoIG(n:FG.node) =
        case FGT.look(cf2igMap, n)
          of SOME node => node
           | NONE => ErrorMsg.impossible ("ig node not found for cf node '" ^ FG.nodename n ^ "'")

      fun tnode(t:T.temp):G.node =
        case TT.look(iGraphNodes, t)
          of SOME node => node
           | NONE => ErrorMsg.impossible ("node not found for temp '" ^ format t ^ "'")

      fun gtemp(n:G.node):T.temp =
        case GT.look(iGraphTemps, n)
          of SOME temp => temp
           | NONE => ErrorMsg.impossible ("node '" ^ G.nodename n ^ "' not found")

      val initOutLiveMap:tempSet.set FGT.table = foldl (fn (n, tbl) => FGT.enter(tbl, n, tempSet.empty)) FGT.empty fgNodes
      val initInLiveMap:tempSet.set FGT.table = foldl (fn (n, tbl) => FGT.enter(tbl, n, tempSet.empty)) FGT.empty fgNodes

      fun repeat(outLiveMap, inLiveMap) =
        let
          fun equal(mapA, mapB) =
            let
              fun same(node) =
                let
                  val listA = tempSet.listItems(valOfFG(mapA, node))
                  val listB = tempSet.listItems(valOfFG(mapB, node))
                in
                  if length listA <> length listB then false
                  else
                    ListPair.allEq (fn (a, b) => a = b) (listA, listB)
                end
            in
              List.all same fgNodes
            end
          fun foreach(n:FG.node, (outLiveMap', inLiveMap')) =
            let
              val ins = valOfFG(inLiveMap, n)
              val outs = valOfFG(outLiveMap, n)

              val inTemps = tempSet.addList(tempSet.difference(valOfFG(outLiveMap, n),
                                                               makeSet(valOfFG(def, n))),
                                           valOfFG(use, n))
              fun unionIn(n', outs) =
                tempSet.union(outs, valOfFG(inLiveMap, n'))
              val outTemps = foldl unionIn tempSet.empty (FG.succ n)
            in
              (FGT.enter(outLiveMap', n, outTemps), FGT.enter(inLiveMap', n, inTemps))
            end
          val (newOutLiveMap, newInLiveMap) = foldl foreach (inLiveMap, outLiveMap) fgNodes
        in
          if equal(newOutLiveMap, outLiveMap) andalso equal(newInLiveMap, inLiveMap) then
            (newOutLiveMap, newInLiveMap)
          else repeat(newOutLiveMap, newInLiveMap)
        end

      val (outLiveMap, inLiveMap) = repeat(initOutLiveMap, initInLiveMap)
      fun doprint(node) =
        let
          val nodeOuts = tempSet.listItems(valOfFG(outLiveMap, node))
          val nodeIns = tempSet.listItems(valOfFG(inLiveMap, node))
          val os = ListFormat.listToString (T.makeString) nodeOuts
          val is = ListFormat.listToString (T.makeString) nodeIns
          val su = ListFormat.listToString (FG.nodename) (FG.succ node)
          val pr = ListFormat.listToString (FG.nodename) (FG.pred node)
          val us = ListFormat.listToString (T.makeString) (valOfFG(use, node))
          val de = ListFormat.listToString (T.makeString) (valOfFG(def, node))
        in
          ErrorMsg.debug (FG.nodename node ^ "-> " ^ assem(node) ^ "  out: " ^ os ^ "\n  ins: " ^ is ^ "\n  succ: " ^ su ^ "\n  pred: " ^ pr ^ "\n  use: " ^ us ^ "\n  def: " ^ de ^ "\n")
        end
      val _ = app doprint fgNodes

      fun getOutLives(node:FG.node):Temp.temp list =
        tempSet.listItems(valOfFG(outLiveMap, node))

      fun genIGraph(h::t:FG.node list, moves) =
            let
              val outs = getOutLives(h)
              val (g, n) = h
              fun conv t =
                let val t' = gtemp t
                in
                  case TT.look(Amd64Frame.tempMap, t')
                    of SOME s => "%" ^ s
                     | NONE => T.makeString t'
                end handle NotFound => "notfound"
            in
              if case FGT.look(ismove, h)
                   of SOME b => b
                    | NONE => ErrorMsg.impossible "node ismove not found" then
                let
                  val a = tnode(
                    case FGT.look(def, h)
                      of SOME t => if length t > 1 then ErrorMsg.impossible "more than one destination in move" else hd t
                       | NONE => ErrorMsg.impossible "destination not found in move CF node")
                  val c = tnode(
                    case FGT.look(use, h)
                      of SOME t => if length t > 1 then ErrorMsg.impossible "more than one source in move" else hd t
                       | NONE => ErrorMsg.impossible "source not found in move CF node")
                  fun addEdge b =
                    let val b' = tnode b
                    in
                      if G.eq(b', c) then ()
                      else
                        G.mk_edge{from=a, to=b'}
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
                          val varNode = tnode var
                          fun mkedges'(out:T.temp) =
                            let
                              val liveNode = tnode out
                            in
                              if G.eq(varNode, liveNode) orelse G.isAdj(varNode, liveNode) then ()
                              else
                                G.mk_edge{from=varNode, to=liveNode}
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

      fun gTemp(node:G.node):T.temp =
        case GT.look(iGraphTemps, node)
          of SOME t => t
           | NONE => ErrorMsg.impossible ("temp -> node '" ^ G.nodename node ^ "' not found")
      fun conv t =
        let val t' = gTemp t
        in
          case TT.look(Amd64Frame.tempMap, t')
            of SOME s => "%" ^ s
             | NONE => T.makeString(t')
        end
    in
      (IGRAPH{graph=iGraph,
              tnode=tnode,
              gtemp=gTemp,
              moves=moves}, getOutLives)
    end

  and show(out, IGRAPH{graph, tnode, gtemp, moves}) =
    let
      val nodeList = G.nodes graph
      val nodeStrings = (fn n => (format (gtemp n)))
      fun nodeStr n =
        nodeStrings n ^ " --> " ^ (ListFormat.listToString nodeStrings (G.adj n))
    in
      TextIO.output(out, String.concatWith "\n" (map nodeStr nodeList) ^ "\n")
    end
end
