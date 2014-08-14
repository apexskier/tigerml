signature MAKEGRAPH =
sig
  val instrs2graph : Assem.instr list -> Flow.flowgraph * Flow.Graph.node list
end

structure MakeGraph : MAKEGRAPH =
struct
  structure A = Assem
  structure G = Flow.Graph
  structure S = Symbol
  structure E = ErrorMsg

  val instrNodeTbl:string G.Table.table ref = ref(G.Table.empty)

  fun instrs2graph instrs =
    let
      val g = G.newGraph()
      val emptyTable = G.Table.empty
      fun iterInstrs(h::t) =
            let
              val ({instrs=instrsTable, def, use, ismove}, nodes) = iterInstrs t
              val node = G.newNode g (* current instruction *)
              val instrsTable' = G.Table.enter(instrsTable, node, h)
            in
              ((case h
                of A.OPER{assem, dst, src, jump} =>
                    (instrNodeTbl := G.Table.enter(!instrNodeTbl, node, assem);
                    {instrs=instrsTable',
                     def=G.Table.enter(def, node, dst),
                     use=G.Table.enter(use, node, src),
                     ismove=G.Table.enter(ismove, node, false)})
                 | A.LABEL{assem, lab} =>
                    (instrNodeTbl := G.Table.enter(!instrNodeTbl, node, assem);
                    {instrs=instrsTable',
                     def=G.Table.enter(def, node, nil),
                     use=G.Table.enter(use, node, nil),
                     ismove=G.Table.enter(ismove, node, false)})
                 | A.MOVE{assem, dst, src} =>
                    (instrNodeTbl := G.Table.enter(!instrNodeTbl, node, assem);
                    {instrs=instrsTable',
                     def=G.Table.enter(def, node, [dst]),
                     use=G.Table.enter(use, node, [src]),
                     ismove=G.Table.enter(ismove, node, true)}), nodes @ [node]))
            end
        | iterInstrs([]) =
            ({instrs=emptyTable, def=emptyTable, use=emptyTable, ismove=emptyTable}, nil)

      val ({instrs=instrsTable, def, use, ismove}, nodes) = iterInstrs instrs

      fun getNode(a::b, l):G.node =
            let
              val instr = G.Table.look(instrsTable, a)
            in
              case instr
                of SOME(A.LABEL{assem, lab}) =>
                  if l = lab then a else getNode(b, l)
                 | SOME _ => getNode(b, l)
                 | NONE => E.impossible ("node for label '" ^ S.name l ^ "' not found")
            end
        | getNode(_, l) = E.impossible ("node for label '" ^ S.name l ^ "' not found")

      fun makeEdges(a::(b::c)) =
            let
              val instr = G.Table.look(instrsTable, a)
            in
              if G.isAdj(a, b) then ()
              else G.mk_edge{from=a, to=b};
              case instr
                of SOME(A.OPER{assem, dst, src, jump}) =>
                  (case jump
                    of SOME labs =>
                      let
                        fun mkedge l =
                          let
                            val b' = getNode(nodes, l)
                          in
                            if G.isAdj(a, b') then ()
                            else G.mk_edge({from=a, to=b'})
                          end
                      in
                        app mkedge labs
                      end
                     | NONE => ())
                 | SOME _ => ()
                 | NONE => ();
              makeEdges(b::c);
              ()
            end
         | makeEdges _ = ()

      fun getAssem(node) =
        case G.Table.look(!instrNodeTbl, node)
          of SOME(assem) => assem
           | NONE => ErrorMsg.impossible "node's assem not found"

      val _ =
        app (fn n => let
          val defs =
            case G.Table.look(def, n)
              of SOME(l) => ListFormat.listToString (Temp.makeString) l
               | NONE => ErrorMsg.impossible "error"
          val uses =
            case G.Table.look(use, n)
              of SOME(l) => ListFormat.listToString (Temp.makeString) l
               | NONE => ErrorMsg.impossible "error"
        in
          print (G.nodename n ^ ": " ^ getAssem n ^ "  use: " ^ uses ^ "\n  def: " ^ defs ^ "\n")
        end) nodes
    in
      makeEdges nodes;
      (Flow.FGRAPH{control=g,
                   def=def,
                   use=use,
                   assem=getAssem,
                   ismove=ismove}, G.nodes g)
    end
end
