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

  fun instrs2graph(instrs) =
    let
      val g = G.newGraph()
      val emptyTable = G.Table.empty
      fun iterInstrs(h::t) =
            let
              val ({instrs=instrsTable, def, use, ismove}, nodes) = iterInstrs(t)
              val node = G.newNode(g) (* current instruction *)
              val instrsTable' = G.Table.enter(instrsTable, node, h)
            in
              ((case h
                of A.OPER{assem, dst, src, jump} =>
                    {instrs=instrsTable',
                     def=G.Table.enter(def, node, dst),
                     use=G.Table.enter(use, node, src),
                     ismove=G.Table.enter(ismove, node, false)}
                 | A.LABEL{assem, lab} =>
                    {instrs=instrsTable',
                     def=G.Table.enter(def, node, nil),
                     use=G.Table.enter(use, node, nil),
                     ismove=G.Table.enter(ismove, node, false)}
                 | A.MOVE{assem, dst, src} =>
                    {instrs=instrsTable',
                     def=G.Table.enter(def, node, [dst]),
                     use=G.Table.enter(use, node, [src]),
                     ismove=G.Table.enter(ismove, node, true)}), nodes @ [node])
            end
        | iterInstrs([]) =
            ({instrs=emptyTable, def=emptyTable, use=emptyTable, ismove=emptyTable}, nil)

      val ({instrs=instrsTable, def, use, ismove}, nodes) = iterInstrs(instrs)

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
              G.mk_edge{from=a, to=b};
              case instr
                of SOME(A.OPER{assem, dst, src, jump}) =>
                  (case jump
                    of SOME labs =>
                      let
                        fun mkedge(l) =
                          G.mk_edge({from=a, to=getNode(nodes, l)})
                      in
                        app mkedge labs
                      end
                     | NONE => ())
                 | SOME _ => ()
                 | NONE => ();
              makeEdges(b::c);
              ()
            end
         | makeEdges(_) = ()
    in
      makeEdges(nodes);
      (Flow.FGRAPH{control=g,
                   def=def,
                   use=use,
                   ismove=ismove}, nil)
    end
end
