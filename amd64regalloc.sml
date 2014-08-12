structure Amd64RegAlloc : REGALLOC =
struct
  structure Frame = Amd64Frame
  structure F = Frame
  structure T = Temp
  structure TT = Temp.Table

  structure FG = Flow.Graph
  structure FGT = FG.Table
  structure IG = Liveness.IGraph
  structure IGT = IG.Table

  type allocation = F.register TT.table

  type move = (T.temp * T.temp)
  fun moveCompare((m11, m12):move, (m21, m22):move) =
    let
      val from = Int.compare(m11, m21)
      and to = Int.compare(m12, m22)
    in
      if from = EQUAL andalso to = EQUAL then EQUAL
      else from
    end

  structure intSet = ListSetFn
    (struct
      type ord_key = int
      val compare = Int.compare
    end)

  structure moveMap = ListMapFn
    (struct
      type ord_key = move
      val compare = moveCompare
    end)
  structure moveSet = ListSetFn
    (struct
      type ord_key = move
      val compare = moveCompare
    end)

  structure nodeMap = ListMapFn
    (struct
      type ord_key = T.temp
      val compare = Int.compare
    end)
  structure nodeSet = ListSetFn
    (struct
      type ord_key = T.temp
      val compare = Int.compare
    end)

  structure edgeMap = ListMapFn
    (struct
      type ord_key = move
      val compare = moveCompare
    end)
  structure edgeSet = ListSetFn
    (struct
      type ord_key = move
      val compare = moveCompare
    end)

  fun printList(set, name) =
    print (name ^ ": " ^ ListFormat.listToString Temp.makeString (set) ^ "\n")
  fun printSet(set, name) =
    printList(nodeSet.listItems(set), name)

  fun alloc(instrs, frame) =
    let
      val k:int = length F.colorables

      (* Node work-lists, sets, and stacks.
      * The following lists and sets are always mutually disjoint and every
      * node is always in exactly one of the sets or lists. *)
      val precolored = ref (nodeSet.addList(nodeSet.empty, F.registerTemps)):nodeSet.set ref (* machine registers, preassigned a color *) (* TODO: remove stack pointer and base pointer from this *)
      val initial = ref nodeSet.empty:nodeSet.set ref (* temporary registers, not precolored and not yet processed *)
      val simplifyWorklist = ref nodeSet.empty:nodeSet.set ref (* Low-degree non-move-related nodes *)
      val freezeWorklist = ref nodeSet.empty:nodeSet.set ref (* Low-degree move-related nodes *)
      val spillWorklist = ref nodeSet.empty:nodeSet.set ref (* High-degree nodes *)
      val spilledNodes = ref nodeSet.empty:nodeSet.set ref (* nodes marked for spilling during this round; initially empty. *)
      val coalescedNodes = ref nodeSet.empty:nodeSet.set ref (* registers that have been coalesced *)
      val coloredNodes = ref nodeSet.empty:nodeSet.set ref (* nodes successfully colored *)
      val selectStack = ref nil:Temp.temp list ref (* stack containing temporaries removed from the graph *)

      (* Move sets
      * There are five sets of move instructions, and every move is in exactly
      * one of these sets (after Build through the end of Main) *)
      val coalescedMoves = ref moveSet.empty:moveSet.set ref (* moves that have been coalesced *)
      val constrainedMoves = ref moveSet.empty:moveSet.set ref (* moves whose source and target interfere *)
      val frozenMoves = ref moveSet.empty:moveSet.set ref (* moves that will no longer be considered for coalescing *)
      val worklistMoves = ref moveSet.empty:moveSet.set ref (* moves enabled for possible coalescing *)
      val activeMoves = ref moveSet.empty:moveSet.set ref (* moves not yet ready for coalescing *)

      (* Other data structures *)
      val adjSet = ref edgeSet.empty:edgeSet.set ref (* the set of interference edges in the graph. *)
      val adjList = ref nodeMap.empty:nodeSet.set nodeMap.map ref (* adjacency list representation of the graph; for each non-precolored temporary u, adjList[u] is the set of nodes that interfere with u *)
      val degree = ref nodeMap.empty:int nodeMap.map ref (* an array containing the current degree of each node *)
      val moveList = ref nodeMap.empty:moveSet.set nodeMap.map ref  (* a mapping from a node to the list of moves it is associated with *)
      val alias = ref nodeMap.empty (* when a move (u, v) has been coalesced, and v put in coalescedNodes, then alias(v) = u *)
      val initokColors = (map (fn x=>x-1) (List.tabulate(length F.registerTemps, fn x => x+1)))
      val colors = ref (foldl nodeMap.insert'
                              nodeMap.empty
                              (ListPair.zip(F.registerTemps, initokColors)))

      val instructions = ref instrs:Assem.instr list ref

      val control = ref (FG.newGraph())
      val def = ref FGT.empty
      val use = ref FGT.empty
      val ismove = ref FGT.empty
      val cfNodes = ref nil

      val graph = ref (IG.newGraph())
      val tnode = ref (fn t => ErrorMsg.impossible "calling tnode illegally")
      val gtemp = ref (fn n => ErrorMsg.impossible "calling gtemp illegally")
      val moves = ref nil
      val getOuts = ref (fn n => ErrorMsg.impossible "calling getOuts illegally")

      fun valOf(a:'a option, id) = (* overridden! *)
        case a
          of SOME(b) => b
           | NONE => raise LibBase.NotFound

      fun checkInvariants() =
        let
          fun degreeInvariant() =
            let
              fun check(u) =
                let
                  val du = valOf(nodeMap.find(!degree, u), "131")
                  val alu = valOf(nodeMap.find(!adjList, u), "133")
                in
                  du = length (nodeSet.listItems(nodeSet.intersection(alu,
                                                                      nodeSet.union(!precolored,
                                                                                    nodeSet.union(!simplifyWorklist,
                                                                                                  nodeSet.union(!freezeWorklist, !spillWorklist))))))
                end
            in
              if nodeSet.all check (nodeSet.union(!simplifyWorklist, nodeSet.union(!freezeWorklist, !spillWorklist))) then ()
              else ErrorMsg.impossible "degreeInvariant failed"
            end
          fun simplifyWorklistInvariant() =
            let
              fun check(u) =
                let
                  val du = valOf(nodeMap.find(!degree, u), "147")
                  val mlu = valOf(nodeMap.find(!moveList, u), "148")
                in
                  du < k orelse moveSet.isEmpty(moveSet.intersection(mlu, moveSet.union(!activeMoves, !worklistMoves)))
                end
            in
              if nodeSet.all check (!simplifyWorklist) then ()
              else ErrorMsg.impossible "simplifyWorklistInvariant failed"
            end
          fun freezeWorklistInvariant() =
            let
              fun check(u) =
                let
                  val du = valOf(nodeMap.find(!degree, u), "160")
                  val mlu = valOf(nodeMap.find(!moveList, u), "161")
                in
                  du < k orelse not(moveSet.isEmpty(moveSet.intersection(mlu, moveSet.union(!activeMoves, !worklistMoves))))
                end
            in
              if nodeSet.all check (!freezeWorklist) then ()
              else ErrorMsg.impossible "freezeWorklistInvariant failed"
            end
          fun spillWorklistInvariant() =
            let
              fun check(u) =
                let
                  val du = valOf(nodeMap.find(!degree, u), "160")
                in
                  du >= k
                end
            in
              if nodeSet.all check (!spillWorklist) then ()
              else ErrorMsg.impossible "freezeWorklistInvariant failed"
            end

          fun v(i) =
            i()
        in
          app v [degreeInvariant, simplifyWorklistInvariant, freezeWorklistInvariant, spillWorklistInvariant]
        end

      val allocation' = ref TT.empty:allocation ref

      fun livenessAnalysis() =
        let
          val _ = print "\n## Control flow graph\n"
          val (cfGraph', cfNodes') = MakeGraph.instrs2graph(!instructions)

          val Flow.FGRAPH{control=control', def=def', use=use', ismove=ismove'} = cfGraph'
          val _ = Flow.show(TextIO.stdOut, cfGraph')

          val _ = print "\n## Interference graph\n"
          val (igraph', getOuts') = Liveness.interferenceGraph(cfGraph')
          val Liveness.IGRAPH{graph=graph', tnode=tnode', gtemp=gtemp', moves=moves'} = igraph'
          val _ = Liveness.show(TextIO.stdOut, igraph')

          val _ = print "\n### Live outs\n"
          val _ =
            let
              fun conv(t) =
                case TT.look(Amd64Frame.tempMap, t)
                  of SOME(s) => "%" ^ s
                   | NONE => T.makeString(t)
              fun printOuts(t) =
                let
                  val outs = getOuts'(t)
                in
                  print (conv (gtemp' t) ^ ": " ^ (ListFormat.listToString conv outs) ^ "\n")
                end
            in
              app printOuts (IG.nodes(graph'))
            end

          val allTemps = nodeSet.addList(nodeSet.empty, map gtemp' (IG.nodes graph'))
          val initial' = nodeSet.difference(allTemps, !precolored);

          val adjEdges = foldl (fn (n, edgs) => foldl (fn (n', edgs') => edgs' @ [(gtemp' n', gtemp' n), (gtemp' n, gtemp' n')]) edgs (IG.adj(n))) nil (IG.nodes(graph'))

          fun forMove((u, v), mapping) =
            let
              val u' = gtemp' u
              val v' = gtemp' v
              val mapping' = nodeMap.insert(mapping, u', nodeSet.add(valOf(nodeMap.find(mapping, u'), "180") handle NotFound => nodeSet.empty, v'))
            in
              nodeMap.insert(mapping', v', nodeSet.add(valOf(nodeMap.find(mapping', v'), "182") handle NotFound => nodeSet.empty, u'))
            end
          val movesInit = foldl forMove nodeMap.empty moves'

          fun getdegree(n) =
            let
              val deg =
                if nodeSet.member(!precolored, gtemp' n) then valOf(Int.maxInt, "221")
                else length(IG.adj n)
            in
              (gtemp' n, deg)
            end

        in
          moveList := foldl nodeMap.insert' nodeMap.empty (map (fn n => (gtemp' n, moveSet.empty)) (IG.nodes graph'));
          adjList := foldl nodeMap.insert' nodeMap.empty (map (fn n => (n, nodeSet.addList(nodeSet.empty, map gtemp' (IG.adj(tnode' n))))) (nodeSet.listItems(initial')));
          degree := foldl nodeMap.insert' nodeMap.empty (map getdegree (IG.nodes graph'));
          colors := foldl nodeMap.insert' nodeMap.empty (ListPair.zip(F.registerTemps, initokColors));

          control := control';
          def := def';
          use := use';
          ismove := ismove';
          cfNodes := cfNodes';

          graph := graph';
          tnode := tnode';
          gtemp := gtemp';
          moves := moves';
          getOuts := getOuts';

          initial := initial';

          adjSet := edgeSet.addList(edgeSet.empty, adjEdges);
          adjList := List.foldl (fn (n, map') => nodeMap.insert(map', n, nodeSet.addList(nodeSet.empty, map gtemp' (IG.adj(tnode' n))))) nodeMap.empty (nodeSet.listItems(!initial));

          print "done with liveness analysis\n"
        end

      val _ = livenessAnalysis()

      (* Utilitites *)
      fun isMove(i) =
        case FGT.look(!ismove, i)
          of SOME b => b
           | NONE => ErrorMsg.impossible "instruction not found"

      fun getUse(n) =
        case FGT.look(!use, n)
          of SOME t => nodeSet.addList(nodeSet.empty, t)
           | NONE => ErrorMsg.impossible "node not found: use"

      fun getDef(n) =
        case FGT.look(!def, n)
          of SOME t => nodeSet.addList(nodeSet.empty, t)
           | NONE => ErrorMsg.impossible "node not found: def"

      fun hd(l:'a list) =
        if length l = 0 then ErrorMsg.impossible "taking hd of list of length zero"
        else List.hd l

      fun tl(l:'a list) =
        if length l < 1 then ErrorMsg.impossible "taking tl of list of less than length 1"
        else List.tl l


      fun main() =
        let
          val _ = print "enter main\n"
          fun repeat() =
            (print "enter repeat\n";
            if not(nodeSet.isEmpty(!simplifyWorklist)) then (simplify(); repeat())
            else if not(moveSet.isEmpty(!worklistMoves)) then (coalesce(); repeat())
            else if not(nodeSet.isEmpty(!freezeWorklist)) then (freeze(); repeat())
            else if not(nodeSet.isEmpty(!spillWorklist)) then (selectSpill(); repeat())
            else ();
            if not(nodeSet.isEmpty(!simplifyWorklist) andalso
                   moveSet.isEmpty(!worklistMoves) andalso
                   nodeSet.isEmpty(!freezeWorklist) andalso
                   nodeSet.isEmpty(!spillWorklist))
              then repeat()
              else print "exit repeat\n")
        in
          livenessAnalysis();
          build();
          makeWorklist();
          repeat();
          assignColors();
          if not(nodeSet.isEmpty(!spilledNodes)) then
            (rewriteProgram(); main())
          else ();
          let
            fun transformRegTemp(t) =
              case TT.look(F.tempMap, t)
                of SOME r => r
                 | NONE => ErrorMsg.impossible "register not found"
            val colorableStrs = map transformRegTemp F.colorables
            fun enterAlloc(n, t) =
              TT.enter(t, n,
                       List.nth(colorableStrs,
                                (valOf(nodeMap.find(!colors, n), "193")) ))
                                  handle NotFound => (print ("issue with " ^ T.makeString n ^ "\n"); t)
          in
            allocation' := nodeSet.foldl enterAlloc F.tempMap (nodeSet.union(!coloredNodes, !coalescedNodes))
          end;
          print "exit main\n"
        end

      and build() =
        (let
          val _ = print "building register allocation stuff\n"
          fun forall(b) =
            let
              val live = ref(nodeSet.addList(nodeSet.empty, (!getOuts)(b)))
            in
              if isMove b then
                let
                  val toList = nodeSet.listItems(getUse b)
                  val frList = nodeSet.listItems(getDef b)
                  val to =
                    if length toList <> 1 then
                      ErrorMsg.impossible "move doesn't have one to"
                    else hd toList
                  val fr =
                    if length frList <> 1 then
                      ErrorMsg.impossible "move doesn't have one from"
                    else hd frList
                  val mv = (to, fr)
                  fun forall''(n) =
                    moveList := nodeMap.insert(!moveList, n, moveSet.add(valOf(nodeMap.find(!moveList, n), "217"), mv))
                in
                  live := nodeSet.difference(!live, getUse b);
                  nodeSet.app forall'' (nodeSet.union(getDef b, getUse b));
                  worklistMoves := moveSet.add(!worklistMoves, mv)
                end
              else ();
              nodeSet.app (fn d => nodeSet.app (fn l => addEdge(l, d)) (!live)) (getDef b);
              live := nodeSet.union(getUse b, nodeSet.difference(!live, getDef b))
            end
        in app forall (!cfNodes) end;
        checkInvariants())

      and addEdge(u, v) =
        if not(edgeSet.member(!adjSet, (u, v))) andalso u <> v then
          (adjSet := edgeSet.addList(!adjSet, [(u, v), (v, u)]);
          if not(nodeSet.member(!precolored, u)) then
            (print ("adding " ^ T.makeString v ^ " to adjList of " ^ T.makeString u);
            adjList := nodeMap.insert(!adjList, u, nodeSet.add(valOf(nodeMap.find(!adjList, u), "233"), v));
            degree := nodeMap.insert(!degree, u, valOf(nodeMap.find(!degree, u), "234") + 1)) else ();
          if not(nodeSet.member(!precolored, v)) then
            (print ("adding " ^ T.makeString u ^ " to adjList of " ^ T.makeString v);
            adjList := nodeMap.insert(!adjList, v, nodeSet.add(valOf(nodeMap.find(!adjList, v), "236"), u));
            degree := nodeMap.insert(!degree, v, valOf(nodeMap.find(!degree, v), "237") + 1)) else ())
        else ()

      and makeWorklist() =
        let
          val _ = print "enter makeWorklist\n"
          fun forall(n) =
            (initial := nodeSet.delete(!initial, n);
            if valOf(nodeMap.find(!degree, n), "244") >= k then
              spillWorklist := nodeSet.add(!spillWorklist, n)
            else if moveRelated n then
              freezeWorklist := nodeSet.add(!freezeWorklist, n)
            else
              (simplifyWorklist := nodeSet.add(!simplifyWorklist, n);
              if nodeSet.member(!precolored, n) then print ("Putting precolored node "^T.makeString n^" in simplifyWorklist!\n") else ()))
        in
          nodeSet.app forall (!initial);
          print "exit makeWorklist\n"
        end

      and adjacent(n) =
        nodeSet.difference(valOf(nodeMap.find(!adjList, n), "255") handle NotFound => nodeSet.empty, nodeSet.addList(!coalescedNodes, !selectStack))

      and nodeMoves(n) =
        moveSet.intersection(valOf(nodeMap.find(!moveList, n), "258"), moveSet.union(!activeMoves, !worklistMoves))

      and moveRelated(n):bool =
        not(moveSet.isEmpty(nodeMoves n))

      and simplify() =
        let
          val n = hd(nodeSet.listItems(!simplifyWorklist))
          val _ = if nodeSet.member(!precolored, n) then print ("Pulling precolored node "^T.makeString n^" from simplifyWorklist!\n") else ();
        in
          simplifyWorklist := nodeSet.delete(!simplifyWorklist, n);
          selectStack := n :: (!selectStack);
          if nodeSet.member(!precolored, n) then print ("Putting precolored node "^T.makeString n^" in selectStack!\n") else ();
          nodeSet.app decrementDegree (adjacent(n))
        end

      and decrementDegree(m) =
        let
          val _ = print "enter decrementDegree\n"
          val d = valOf(nodeMap.find(!degree, m), "274")
        in
          degree := nodeMap.insert(!degree, m, d - 1);
          if d = k then
            (enableMoves(nodeSet.add(adjacent(m), m));
            spillWorklist := nodeSet.delete(!spillWorklist, m) handle NotFound => (
              print ("looking for node " ^ T.makeString m ^ "\n");
              printSet(!precolored, "precolored");
              printSet(!initial, "initial");
              printSet(!simplifyWorklist, "simplifyWorklist");
              printSet(!freezeWorklist, "freezeWorklist");
              printSet(!spillWorklist, "spillWorklist");
              printSet(!spilledNodes, "spilledNodes");
              printSet(!coalescedNodes, "coalescedNodes");
              printSet(!coloredNodes, "coloredNodes")
              (* ErrorMsg.impossible "testing" *));
            if moveRelated m then
              freezeWorklist := nodeSet.add(!freezeWorklist, m)
            else
              (simplifyWorklist := nodeSet.add(!simplifyWorklist, m);
              if nodeSet.member(!precolored, m) then print ("Putting precolored node "^T.makeString m^" in simplifyWorklist!\n") else ()))
          else ();
          print "exit decrementDegree\n"
        end

      and enableMoves(nodes) =
        let
          val _ = print "enter enableMoves\n"
          fun forall(n) =
            let
              fun forall'(m) =
                if moveSet.member(!activeMoves, m) then
                  (activeMoves := moveSet.delete(!activeMoves, m);
                  worklistMoves := moveSet.add(!worklistMoves, m))
                else ()
            in
              moveSet.app forall' (nodeMoves(n))
            end
        in nodeSet.app forall nodes;print "exit enableMoves\n" end

      and coalesce() =
        let
          val _ = print "enter coalesce\n"
          val m as (x', y') = hd(moveSet.listItems(!worklistMoves))
          val x = getAlias x'
          val y = getAlias y'
          val (u, v) =
            if nodeSet.member(!precolored, y) then
              (y, x)
            else
              (x, y)
        in
          print "enter in of coalesce\n";
          worklistMoves := moveSet.delete(!worklistMoves, m);
          if u = v then
            (coalescedMoves := moveSet.add(!coalescedMoves, m);
            addWorkList(u))
          else if nodeSet.member(!precolored, v) orelse edgeSet.member(!adjSet, (u, v)) then
            (constrainedMoves := moveSet.add(!constrainedMoves, m);
            addWorkList(u); addWorkList(v))
          else if (not(nodeSet.member(!precolored, u)) andalso (List.all (fn t => ok(t, u)) (nodeSet.listItems(adjacent(v))))) (* NOTE: the membership test for precolored nodes here is different from the book. I am restricting *)
                  orelse (not(nodeSet.member(!precolored, u)) andalso conservative(nodeSet.union(adjacent(u), adjacent(v)))) then
            (coalescedMoves := moveSet.add(!coalescedMoves, m);
            combine(u, v);
            addWorkList(u))
          else activeMoves := moveSet.add(!activeMoves, m);
          print "exit coalesce\n"
        end

      and addWorkList(u) =
        (print "enter addWorkList\n";
        if not(nodeSet.member(!precolored, u)) andalso not(moveRelated u) andalso valOf(nodeMap.find(!degree, u), "327") < k then
          (freezeWorklist := nodeSet.delete(!freezeWorklist, u)
            handle NotFound => print ("T.makeString " ^ T.makeString u ^ " not found in spillWorklist\n");
          simplifyWorklist := nodeSet.add(!simplifyWorklist, u))
        else ();
        print "exit addWorkList\n")

      and ok(t, r) =
        valOf(nodeMap.find(!degree, t), "333") < k orelse nodeSet.member(!precolored, t) orelse edgeSet.member(!adjSet, (t, r))

      and conservative(nodes) =
        let
          val _ = print "enter conservative\n"
          val k' = ref 0
          fun forall(n) =
            if valOf(nodeMap.find(!degree, n), "339") >= k then k' := !k' + 1 else ()
        in
          nodeSet.app forall nodes;
          print "exit conservative\n";
          !k' < k
        end

      and getAlias(n) =
        if nodeSet.member(!coalescedNodes, n) then
          getAlias(valOf(nodeMap.find(!alias, n), "347"))
        else n

      and combine(u, v) =
        (print "enter combine\n";
        if nodeSet.member(!freezeWorklist, v) then
          freezeWorklist := nodeSet.delete(!freezeWorklist, v)
        else
          spillWorklist := nodeSet.delete(!spillWorklist, v)
          handle NotFound => print (T.makeString v ^ " not found in spillWorklist\n");
        print ("adding "^T.makeString v^" to coalescedNodes\n");
        coalescedNodes := nodeSet.add(!coalescedNodes, v);
        alias := nodeMap.insert(!alias, v, u);
        moveList := nodeMap.insert(!moveList, u, moveSet.union(valOf(nodeMap.find(!moveList, u), "357"), valOf(nodeMap.find(!moveList, v), "357b")));
        enableMoves(nodeSet.singleton v);
        nodeSet.app (fn t => (addEdge(t, u); decrementDegree(t))) (adjacent v);
        if valOf(nodeMap.find(!degree, u), "360") >= k andalso nodeSet.member(!freezeWorklist, u) then
          (freezeWorklist := nodeSet.delete(!freezeWorklist, u);
          spillWorklist := nodeSet.add(!spillWorklist, u))
        else ();
        print "exit combine\n")

      and freeze() =
        let
          val _ = print "enter freeze\n"
          val u = hd(nodeSet.listItems(!freezeWorklist))
        in
          freezeWorklist := nodeSet.delete(!freezeWorklist, u);
          simplifyWorklist := nodeSet.add(!simplifyWorklist, u);
          if nodeSet.member(!precolored, u) then print ("Putting precolored node "^T.makeString u^" in simplifyWorklist!\n") else ();
          freezeMoves(u);
          print "exit freeze\n"
        end

      and freezeMoves(u) =
        let
          val _ = print "enter freezeMoves\n"
          fun forall(m as (x, y)) =
            let
              val v =
                if (getAlias y) = (getAlias u) then
                  getAlias x
                else
                  getAlias y
            in
              activeMoves := moveSet.delete(!activeMoves, m) handle NotFound => print "freezemoves notfound a\n";
              frozenMoves := moveSet.add(!frozenMoves, m);
              if moveSet.isEmpty(nodeMoves v) andalso valOf(nodeMap.find(!degree, v), "386") < k then
                (freezeWorklist := nodeSet.delete(!freezeWorklist, v) handle NotFound => print "freezemoves notfound b\n";
                simplifyWorklist := nodeSet.add(!simplifyWorklist, v);
                if nodeSet.member(!precolored, v) then print ("Putting precolored node "^T.makeString v^" in simplifyWorklist as a result of "^T.makeString u^" (freezeMoves)!\n") else ())
              else ()
            end
        in
          moveSet.app forall (nodeMoves u);
          print "exit freezeMoves\n"
        end

      and selectSpill() =
        let
          val _ = print "enter selectSpill\n"
          val m = hd(nodeSet.listItems(!spillWorklist)) (* from book:
                                                         * "select using favoriate heuristic. Note: avoid choosing nodes that
                                                         * are the tiny live ranges resulting from the fetches of previously
                                                         * spilled registers" *)
        in
          spillWorklist := nodeSet.delete(!spillWorklist, m);
          simplifyWorklist := nodeSet.add(!simplifyWorklist, m);
          if nodeSet.member(!precolored, m) then print ("Putting precolored node "^T.makeString m^" in simplifyWorklist!\n") else ();
          freezeMoves(m);
          print "exit selectSpill\n"
        end

      and assignColors() =
        (while not(null(!selectStack)) do
          let
            val n =
              let val n' = hd(!selectStack)
              in selectStack := tl(!selectStack); n' end
            val _ = if nodeSet.member(!precolored, n) then print ("Putting precolored node "^T.makeString n^" in coloredNodes!\n") else ();
            val i = ref 0
            val okColors = ref (intSet.addList(intSet.empty, initokColors))
            fun forall(w) =
              if nodeSet.member((nodeSet.union(!coloredNodes, !precolored)), getAlias w) then
                let
                  val a = valOf(nodeMap.find(!colors, getAlias w), "417") handle NotFound => ErrorMsg.impossible(T.makeString(getAlias w) ^ " has no color")
                in
                  print ("deleting color " ^ Int.toString a ^ " from okColors\n");
                  okColors := intSet.delete(!okColors, a)
                  handle NotFound => print (T.makeString a ^ " not found in assignColors\n")
                end
              else ()
          in
            print ("Doing " ^ T.makeString n ^ "\n");
            nodeSet.app forall (valOf(nodeMap.find(!adjList, n), "420") handle NotFound => nodeSet.empty);
            if intSet.isEmpty(!okColors) then
              (spilledNodes := nodeSet.add(!spilledNodes, n);
              print ("spilling " ^ T.makeString n ^ "\n"))
            else
              let
                val c = hd(intSet.listItems(!okColors))
              in
                print ("assigning color " ^ Int.toString c ^ " to " ^ T.makeString n ^ "\n");
                coloredNodes := nodeSet.add(!coloredNodes, n);
                colors := nodeMap.insert(!colors, n, c)
              end
          end;
        let
          fun addCoalescedColor(n) =
            let
              val c = valOf(nodeMap.find(!colors, getAlias n), "432") handle NotFound => ErrorMsg.impossible(T.makeString(getAlias n) ^ " has no color.")
            in
              print ("assigning color " ^ Int.toString c ^ " to " ^ T.makeString n ^ " from " ^ T.makeString(getAlias n) ^ " (c)\n");
              colors := nodeMap.insert(!colors, n, c)
            end
        in
          nodeSet.app addCoalescedColor (!coalescedNodes);
          print "-------\n"
        end)

      and rewriteProgram() =
        let
          val _ = print "enter rewriteProgram\n"
          fun foreachSpill(node:FG.node, newtemps':nodeSet.set) =
            let
              val access = F.allocLocal(frame)(true)
              val defs = getDef node
              val uses = getUse node
              fun idx(item, ls) =
                let
                  fun idx'(m, nil) = 0
                    | idx'(m, h::t) = if FG.eq(h, item) then m else idx'(m+1, t)
                in
                  idx'(0, ls)
                end
              fun insertInstr(instrs, node, bfr:bool) =
                let
                  val nodeIdx = idx(!tnode node, !cfNodes) - (if bfr then 1 else 0)
                  val newnodes = List.map (fn _ => FG.newNode(!control)) instrs
                in
                  cfNodes := (List.take(!cfNodes, nodeIdx)) @ newnodes @ (List.drop(!cfNodes, nodeIdx));
                  print "inserting some instructions\n";
                  instructions := (List.take(!instructions, nodeIdx)) @ instrs @ (List.drop(!instructions, nodeIdx))
                end
              fun forEachDef(var, newtemps) =
                let
                  val newtemp = T.newTemp()
                  val _ = print ("made new temp " ^ T.makeString newtemp)
                  val tree = Tree.MOVE(Tree.TEMP newtemp, F.exp(access)(Tree.TEMP F.FP))
                  val instrs = Amd64Codegen.codegen frame tree
                in
                  insertInstr(instrs, var, false);
                  nodeSet.add(newtemps, newtemp)
                end
              fun forEachUse(var, newtemps) =
                let
                  val newtemp = T.newTemp()
                  val _ = print ("made new temp " ^ T.makeString newtemp)
                  val tree = Tree.MOVE(F.exp(access)(Tree.TEMP F.FP), Tree.TEMP newtemp)
                  val instrs = Amd64Codegen.codegen frame tree
                in
                  insertInstr(instrs, var, true);
                  nodeSet.add(newtemps, newtemp)
                end
            in
              nodeSet.foldl forEachDef (nodeSet.foldl forEachUse newtemps' uses) defs
            end
          val newTemps = List.foldl foreachSpill nodeSet.empty (List.map (fn t => !tnode t) (nodeSet.listItems(!spilledNodes)))
        in
        (* TODO:
        * Allocate memory locations for each v in spilledNodes.
        * Create a new temporary vi for each definition and each use.
        * In the program (instructions), insert a store after each definition of a vi, a fetch before each use of a vi.
        * Put all the vi into a set newTemps.
        * *)
          spilledNodes := nodeSet.empty;
          initial := nodeSet.union(!coloredNodes, nodeSet.union(!coalescedNodes, newTemps));
          coloredNodes := nodeSet.empty;
          coalescedNodes := nodeSet.empty;
          print "exit rewriteProgram\n"
        end
    in
      main();
      printSet(!precolored, "precolored");
      printSet(!initial, "initial");
      printSet(!simplifyWorklist, "simplifyWorklist");
      printSet(!freezeWorklist, "freezeWorklist");
      printSet(!spillWorklist, "spillWorklist");
      printSet(!spilledNodes, "spilledNodes");
      printSet(!coalescedNodes, "coalescedNodes");
      printSet(!coloredNodes, "coloredNodes");
      (!instructions, !allocation')
    end
end

