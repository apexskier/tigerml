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

  structure E = ErrorMsg

  type allocation = F.register TT.table

  fun format(t) =
    case Temp.Table.look(F.tempMap, t)
      of SOME(s) => "%" ^ s
       | NONE => Temp.makeString(t)

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

  fun alloc(instrs, frame, prcfgraph, prigraph, prliveout) =
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
      val initok =
        let
          fun test(color:int, colors:int list):int list =
            let
              val colorTemp = List.nth(F.registerTemps, color)
              fun eq(x:T.temp) =
                x = colorTemp
            in
              if List.exists eq F.colorables then color::colors else colors
            end
        in
          foldl test [] initokColors
        end
      val _ = E.debug ("initokColors: " ^ ListFormat.listToString (Int.toString) initokColors ^ "\n")
      val _ = E.debug ("initok: " ^ ListFormat.listToString (Int.toString) initok ^ "\n")
      val _ = E.debug ("initok: " ^ ListFormat.listToString (fn a => List.nth(F.registers, a)) initok ^ "\n")
      val colors = ref (foldl nodeMap.insert'
                              nodeMap.empty
                              (ListPair.zip(F.registerTemps, (map (fn x=>x-1) (List.tabulate(length F.registerTemps, fn x => x+1))))))

      val instructions = ref instrs:Assem.instr list ref

      val control = ref (FG.newGraph())
      val def = ref FGT.empty
      val use = ref FGT.empty
      val ismove = ref FGT.empty
      val cfNodes = ref nil

      val graph = ref (IG.newGraph())
      val tnode = ref (fn t => E.impossible "calling tnode illegally")
      val gtemp = ref (fn n => E.impossible "calling gtemp illegally")
      val moves = ref nil
      val getOuts = ref (fn n => E.impossible "calling getOuts illegally")

      fun valOf(a:'a option) = (* overridden! *)
        case a
          of SOME b => b
           | NONE => raise LibBase.NotFound

      fun checkInvariants() =
        let
          fun degreeInvariant() =
            let
              fun check u =
                let
                  val du = valOf(nodeMap.find(!degree, u))
                  val alu = valOf(nodeMap.find(!adjList, u))
                in
                  du = length (nodeSet.listItems(nodeSet.intersection(alu,
                                                                      nodeSet.union(!precolored,
                                                                                    nodeSet.union(!simplifyWorklist,
                                                                                                  nodeSet.union(!freezeWorklist, !spillWorklist))))))
                end
            in
              if nodeSet.all check (nodeSet.union(!simplifyWorklist, nodeSet.union(!freezeWorklist, !spillWorklist))) then ()
              else E.impossible "degreeInvariant failed"
            end
          fun simplifyWorklistInvariant() =
            let
              fun check u =
                let
                  val du = valOf(nodeMap.find(!degree, u))
                  val mlu = valOf(nodeMap.find(!moveList, u))
                in
                  du < k orelse moveSet.isEmpty(moveSet.intersection(mlu, moveSet.union(!activeMoves, !worklistMoves)))
                end
            in
              if nodeSet.all check (!simplifyWorklist) then ()
              else E.impossible "simplifyWorklistInvariant failed"
            end
          fun freezeWorklistInvariant() =
            let
              fun check u =
                let
                  val du = valOf(nodeMap.find(!degree, u))
                  val mlu = valOf(nodeMap.find(!moveList, u))
                in
                  du < k orelse not(moveSet.isEmpty(moveSet.intersection(mlu, moveSet.union(!activeMoves, !worklistMoves))))
                end
            in
              if nodeSet.all check (!freezeWorklist) then ()
              else E.impossible "freezeWorklistInvariant failed"
            end
          fun spillWorklistInvariant() =
            let
              fun check u =
                let
                  val du = valOf(nodeMap.find(!degree, u))
                in
                  du >= k
                end
            in
              if nodeSet.all check (!spillWorklist) then ()
              else E.impossible "freezeWorklistInvariant failed"
            end

          fun v i =
            i()
        in
          app v [degreeInvariant, simplifyWorklistInvariant, freezeWorklistInvariant, spillWorklistInvariant]
        end

      val allocation' = ref TT.empty:allocation ref

      fun livenessAnalysis() =
        let
          val (cfGraph', cfNodes') = MakeGraph.instrs2graph(!instructions)

          val Flow.FGRAPH{control=control', def=def', use=use', assem=assem', ismove=ismove'} = cfGraph'
          val _ =
            if prcfgraph then
              (print "Control Flow Graph\n";
              Flow.show(TextIO.stdOut, cfGraph'))
            else ()

          val (igraph', getOuts') = Liveness.interferenceGraph(cfGraph')
          val Liveness.IGRAPH{graph=graph', tnode=tnode', gtemp=gtemp', moves=moves'} = igraph'
          val _ =
            if prigraph then
              (print "Interference graph\n";
              Liveness.show(TextIO.stdOut, igraph');
              print "\n")
            else ()

          val _ =
            if prliveout then
              (print "Live outs:\n";
              let
                fun conv t =
                  case TT.look(Amd64Frame.tempMap, t)
                    of SOME s => "%" ^ s
                     | NONE => format t
                fun printOuts t =
                  let
                    val outs = getOuts'(t)
                  in
                    print (conv (gtemp' t) ^ ": " ^ (ListFormat.listToString conv outs) ^ "\n")
                  end
              in
                app printOuts (IG.nodes(graph'))
              end;
              print "\n")
            else ()

          val allTemps = nodeSet.addList(nodeSet.empty, map gtemp' (IG.nodes graph'))
          val initial' = nodeSet.difference(allTemps, !precolored);

          val adjEdges = foldl (fn (n, edgs) => foldl (fn (n', edgs') => edgs' @ [(gtemp' n', gtemp' n), (gtemp' n, gtemp' n')]) edgs (IG.adj n)) nil (IG.nodes(graph'))

          fun forMove((u, v), mapping) =
            let
              val u' = gtemp' u
              val v' = gtemp' v
              val mapping' = nodeMap.insert(mapping, u', nodeSet.add(valOf(nodeMap.find(mapping, u')) handle NotFound => nodeSet.empty, v'))
            in
              nodeMap.insert(mapping', v', nodeSet.add(valOf(nodeMap.find(mapping', v')) handle NotFound => nodeSet.empty, u'))
            end
          val movesInit = foldl forMove nodeMap.empty moves'

          fun getdegree n =
            let
              val deg =
                if nodeSet.member(!precolored, gtemp' n) then valOf(Int.maxInt)
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

          E.debug "done with liveness analysis\n"
        end

      (* Utilitites *)
      fun isMove i =
        case FGT.look(!ismove, i)
          of SOME b => b
           | NONE => E.impossible "instruction not found"

      fun getUse n =
        case FGT.look(!use, n)
          of SOME t => nodeSet.addList(nodeSet.empty, t)
           | NONE => E.impossible "node not found: use"

      fun getDef n =
        case FGT.look(!def, n)
          of SOME t => nodeSet.addList(nodeSet.empty, t)
           | NONE => E.impossible "node not found: def"

      fun hd(l:'a list) =
        if length l = 0 then E.impossible "taking hd of list of length zero"
        else List.hd l

      fun tl(l:'a list) =
        if length l < 1 then E.impossible "taking tl of list of less than length 1"
        else List.tl l


      fun main() =
        let
          val _ = E.debug "enter main\n"
          fun repeat() =
            (E.debug "enter repeat\n";
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
              else E.debug "exit repeat\n")
        in
          livenessAnalysis();
          build();
          makeWorklist();
          repeat();
          assignColors();
          if not(nodeSet.isEmpty(!spilledNodes)) then
            (rewriteProgram();
            main())
          else ();
          let
            fun transformRegTemp t =
              case TT.look(F.tempMap, t)
                of SOME r => r
                 | NONE => E.impossible "register not found"
            val colorableStrs = map transformRegTemp F.registerTemps
            fun enterAlloc(n, t) =
              TT.enter(t, n,
                       List.nth(colorableStrs,
                                valOf(nodeMap.find(!colors, n)
                       handle NotFound => E.impossible("couldn't find assigned color for temp " ^ format n))))
              handle NotFound => E.impossible ("assigned a non-existant color '" ^ Int.toString(valOf(nodeMap.find(!colors, n))) ^ "' to temp '" ^ format n ^ "'")
          in
            allocation' := nodeSet.foldl enterAlloc F.tempMap (nodeSet.union(!coloredNodes, !coalescedNodes))
          end;
          E.debug "exit main\n"
        end

      and build() =
        (let
          val _ = E.debug "building register allocation stuff\n"
          fun forall b =
            let
              val live = ref(nodeSet.addList(nodeSet.empty, (!getOuts)(b)))
            in
              if isMove b then
                let
                  val toList = nodeSet.listItems(getUse b)
                  val frList = nodeSet.listItems(getDef b)
                  val to =
                    if length toList <> 1 then
                      E.impossible "move doesn't have one to"
                    else hd toList
                  val fr =
                    if length frList <> 1 then
                      E.impossible "move doesn't have one from"
                    else hd frList
                  val mv = (to, fr)
                  fun forall''(n) =
                    moveList := nodeMap.insert(!moveList, n, moveSet.add(valOf(nodeMap.find(!moveList, n)), mv))
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
            (E.debug ("adding " ^ format v ^ " to adjList of " ^ format u);
            adjList := nodeMap.insert(!adjList, u, nodeSet.add(valOf(nodeMap.find(!adjList, u)), v));
            degree := nodeMap.insert(!degree, u, valOf(nodeMap.find(!degree, u)) + 1)) else ();
          if not(nodeSet.member(!precolored, v)) then
            (E.debug ("adding " ^ format u ^ " to adjList of " ^ format v);
            adjList := nodeMap.insert(!adjList, v, nodeSet.add(valOf(nodeMap.find(!adjList, v)), u));
            degree := nodeMap.insert(!degree, v, valOf(nodeMap.find(!degree, v)) + 1)) else ())
        else ()

      and makeWorklist() =
        let
          val _ = E.debug "enter makeWorklist\n"
          fun forall n =
            (initial := nodeSet.delete(!initial, n);
            if valOf(nodeMap.find(!degree, n)) >= k then
              spillWorklist := nodeSet.add(!spillWorklist, n)
            else if moveRelated n then
              freezeWorklist := nodeSet.add(!freezeWorklist, n)
            else
              (simplifyWorklist := nodeSet.add(!simplifyWorklist, n);
              if nodeSet.member(!precolored, n) then E.debug ("Putting precolored node "^format n^" in simplifyWorklist!\n") else ()))
        in
          nodeSet.app forall (!initial);
          E.debug "exit makeWorklist\n"
        end

      and adjacent n =
        nodeSet.difference(valOf(nodeMap.find(!adjList, n)) handle NotFound => nodeSet.empty, nodeSet.addList(!coalescedNodes, !selectStack))

      and nodeMoves n =
        moveSet.intersection(valOf(nodeMap.find(!moveList, n)), moveSet.union(!activeMoves, !worklistMoves))

      and moveRelated n =
        not(moveSet.isEmpty(nodeMoves n))

      and simplify() =
        let
          val n = hd(nodeSet.listItems(!simplifyWorklist))
          val _ = if nodeSet.member(!precolored, n) then E.debug ("Pulling precolored node "^format n^" from simplifyWorklist!\n") else ();
        in
          simplifyWorklist := nodeSet.delete(!simplifyWorklist, n);
          selectStack := n :: (!selectStack);
          if nodeSet.member(!precolored, n) then E.debug ("Putting precolored node "^format n^" in selectStack!\n") else ();
          nodeSet.app decrementDegree (adjacent n)
        end

      and decrementDegree m =
        let
          val _ = E.debug "enter decrementDegree\n"
          val d = valOf(nodeMap.find(!degree, m))
        in
          degree := nodeMap.insert(!degree, m, d - 1);
          if d = k then
            (enableMoves(nodeSet.add(adjacent m, m));
            spillWorklist := nodeSet.delete(!spillWorklist, m) handle NotFound => (
              E.debug ("looking for node " ^ format m ^ "\n")
              (* E.impossible "testing" *));
            if moveRelated m then
              freezeWorklist := nodeSet.add(!freezeWorklist, m)
            else
              (simplifyWorklist := nodeSet.add(!simplifyWorklist, m);
              if nodeSet.member(!precolored, m) then E.debug ("Putting precolored node "^format m^" in simplifyWorklist!\n") else ()))
          else ();
          E.debug "exit decrementDegree\n"
        end

      and enableMoves nodes =
        let
          val _ = E.debug "enter enableMoves\n"
          fun forall n =
            let
              fun forall'(m) =
                if moveSet.member(!activeMoves, m) then
                  (activeMoves := moveSet.delete(!activeMoves, m);
                  worklistMoves := moveSet.add(!worklistMoves, m))
                else ()
            in
              moveSet.app forall' (nodeMoves n)
            end
        in nodeSet.app forall nodes;E.debug "exit enableMoves\n" end

      and coalesce() =
        let
          val _ = E.debug "enter coalesce\n"
          val m as (x', y') = hd(moveSet.listItems(!worklistMoves))
          val x = getAlias x'
          val y = getAlias y'
          val (u, v) =
            if nodeSet.member(!precolored, y) then
              (y, x)
            else
              (x, y)
        in
          E.debug "enter in of coalesce\n";
          worklistMoves := moveSet.delete(!worklistMoves, m);
          if u = v then
            (coalescedMoves := moveSet.add(!coalescedMoves, m);
            addWorkList u)
          else if nodeSet.member(!precolored, v) orelse edgeSet.member(!adjSet, (u, v)) then
            (constrainedMoves := moveSet.add(!constrainedMoves, m);
            addWorkList u; addWorkList v)
          else if (not(nodeSet.member(!precolored, u)) andalso (List.all (fn t => ok(t, u)) (nodeSet.listItems(adjacent v)))) (* NOTE: the membership test for precolored nodes here is different from the book. I am restricting *)
                  orelse (not(nodeSet.member(!precolored, u)) andalso conservative(nodeSet.union(adjacent u, adjacent v))) then
            (coalescedMoves := moveSet.add(!coalescedMoves, m);
            combine(u, v);
            addWorkList u)
          else activeMoves := moveSet.add(!activeMoves, m);
          E.debug "exit coalesce\n"
        end

      and addWorkList u =
        (E.debug "enter addWorkList\n";
        if not(nodeSet.member(!precolored, u)) andalso not(moveRelated u) andalso valOf(nodeMap.find(!degree, u)) < k then
          (freezeWorklist := nodeSet.delete(!freezeWorklist, u)
            handle NotFound => E.impossible ("format " ^ format u ^ " not found in spillWorklist\n");
          simplifyWorklist := nodeSet.add(!simplifyWorklist, u))
        else ();
        E.debug "exit addWorkList\n")

      and ok(t, r) =
        valOf(nodeMap.find(!degree, t)) < k orelse nodeSet.member(!precolored, t) orelse edgeSet.member(!adjSet, (t, r))

      and conservative nodes =
        let
          val _ = E.debug "enter conservative\n"
          val k' = ref 0
          fun forall n =
            if valOf(nodeMap.find(!degree, n)) >= k then k' := !k' + 1 else ()
        in
          nodeSet.app forall nodes;
          E.debug "exit conservative\n";
          !k' < k
        end

      and getAlias n =
        if nodeSet.member(!coalescedNodes, n) then
          getAlias(valOf(nodeMap.find(!alias, n)))
        else n

      and combine(u, v) =
        (E.debug "enter combine\n";
        if nodeSet.member(!freezeWorklist, v) then
          freezeWorklist := nodeSet.delete(!freezeWorklist, v)
        else
          spillWorklist := nodeSet.delete(!spillWorklist, v)
          handle NotFound => E.impossible (format v ^ " not found in spillWorklist\n");
        E.debug ("adding "^format v^" to coalescedNodes\n");
        coalescedNodes := nodeSet.add(!coalescedNodes, v);
        alias := nodeMap.insert(!alias, v, u);
        moveList := nodeMap.insert(!moveList, u, moveSet.union(valOf(nodeMap.find(!moveList, u)), valOf(nodeMap.find(!moveList, v))));
        enableMoves(nodeSet.singleton v);
        nodeSet.app (fn t => (addEdge(t, u); decrementDegree t)) (adjacent v);
        if valOf(nodeMap.find(!degree, u)) >= k andalso nodeSet.member(!freezeWorklist, u) then
          (freezeWorklist := nodeSet.delete(!freezeWorklist, u);
          spillWorklist := nodeSet.add(!spillWorklist, u))
        else ();
        E.debug "exit combine\n")

      and freeze() =
        let
          val _ = E.debug "enter freeze\n"
          val u = hd(nodeSet.listItems(!freezeWorklist))
        in
          freezeWorklist := nodeSet.delete(!freezeWorklist, u);
          simplifyWorklist := nodeSet.add(!simplifyWorklist, u);
          if nodeSet.member(!precolored, u) then E.debug ("Putting precolored node "^format u^" in simplifyWorklist!\n") else ();
          freezeMoves u;
          E.debug "exit freeze\n"
        end

      and freezeMoves u =
        let
          val _ = E.debug "enter freezeMoves\n"
          fun forall(m as (x, y)) =
            let
              val v =
                if (getAlias y) = (getAlias u) then
                  getAlias x
                else
                  getAlias y
            in
              activeMoves := moveSet.delete(!activeMoves, m) handle NotFound => E.debug "freezemoves notfound a\n";
              frozenMoves := moveSet.add(!frozenMoves, m);
              if moveSet.isEmpty(nodeMoves v) andalso valOf(nodeMap.find(!degree, v)) < k then
                (freezeWorklist := nodeSet.delete(!freezeWorklist, v) handle NotFound => E.debug "freezemoves notfound b\n";
                simplifyWorklist := nodeSet.add(!simplifyWorklist, v);
                if nodeSet.member(!precolored, v) then E.debug ("Putting precolored node "^format v^" in simplifyWorklist as a result of "^format u^" (freezeMoves)!\n") else ())
              else ()
            end
        in
          moveSet.app forall (nodeMoves u);
          E.debug "exit freezeMoves\n"
        end

      and selectSpill() =
        let
          val _ = E.debug "enter selectSpill\n"
          val m = hd(nodeSet.listItems(!spillWorklist)) (* from book:
                                                         * "select using favoriate heuristic. Note: avoid choosing nodes that
                                                         * are the tiny live ranges resulting from the fetches of previously
                                                         * spilled registers" *)
        in
          E.debug ("selecting node to spill: " ^ format m ^ "\n");
          spillWorklist := nodeSet.delete(!spillWorklist, m);
          simplifyWorklist := nodeSet.add(!simplifyWorklist, m);
          if nodeSet.member(!precolored, m) then E.debug ("Putting precolored node "^format m^" in simplifyWorklist!\n") else ();
          freezeMoves m;
          E.debug "exit selectSpill\n"
        end

      and assignColors() =
        (while not(null(!selectStack)) do
          let
            val n =
              let val n' = hd(!selectStack)
              in selectStack := tl(!selectStack); n' end
            val _ =
              if nodeSet.member(!precolored, n) then
                E.debug ("Putting precolored node "^format n^" in coloredNodes!\n")
              else ()
            val i = ref 0
            val okColors = ref (intSet.addList(intSet.empty, initok))
            fun forall w =
              if nodeSet.member((nodeSet.union(!coloredNodes, !precolored)), getAlias w) then
                let
                  val a = valOf(nodeMap.find(!colors, getAlias w))
                    handle NotFound => E.impossible(format(getAlias w) ^ " has no color")
                in
                  E.debug ("deleting color " ^ Int.toString a ^ " ("^ List.nth(F.registers, a) ^") from okColors\n");
                  okColors := intSet.delete(!okColors, a)
                  handle NotFound => E.debug (format a ^ " not found in assignColors\n")
                end
              else ()
          in
            E.debug ("Doing " ^ format n ^ "\n");
            nodeSet.app forall (valOf(nodeMap.find(!adjList, n)) handle NotFound => nodeSet.empty);
            if intSet.isEmpty(!okColors) then
              (E.debug ("spilling " ^ format n ^ "\n");
              spilledNodes := nodeSet.add(!spilledNodes, n))
            else
              let
                val c = hd(intSet.listItems(!okColors))
              in
                E.debug ("assigning color " ^ Int.toString c ^ " ("^ List.nth(F.registers, c) ^") to " ^ format n ^ "\n");
                coloredNodes := nodeSet.add(!coloredNodes, n);
                colors := nodeMap.insert(!colors, n, c)
              end
          end;
        let
          fun addCoalescedColor n =
            let
              val c = valOf(nodeMap.find(!colors, getAlias n))
                handle NotFound => E.impossible(format(getAlias n) ^ " has no color.")
            in
              E.debug ("assigning color " ^ Int.toString c ^ " to " ^ format n ^ " from " ^ format(getAlias n) ^ " (c)\n");
              colors := nodeMap.insert(!colors, n, c)
            end
        in
          nodeSet.app addCoalescedColor (!coalescedNodes);
          E.debug "-------\n"
        end)

      and rewriteProgram() =
        let
          val _ = E.debug "enter rewriteProgram\n"
          fun idx(item, ls) =
            let
              fun idx'(m, nil) = 0
                | idx'(m, h::t) = if FG.eq(h, item) then m else idx'(m+1, t)
            in
              idx'(0, ls)
            end
          (* val newInstructions = !instructions
          val addedInstructions = ref 0 *)
          fun foreachSpill(temp) =
            let
              val nodeIdx = idx(!tnode temp, !cfNodes)
              val _ = E.debug ("rewriting for temp '" ^ Temp.makeString temp ^ "' " ^ Int.toString nodeIdx ^ "\n")
              val access = F.allocLocal(frame)(true)

              fun iterInstructions(instr, instrs) =
                let
                  fun foreach(dst, src) =
                    let
                      fun d(instrs, instr') =
                        if List.exists (fn t => t = temp) dst then
                          let
                            val newtemp = Temp.newTemp()
                            val newdst = List.map (fn t => if t = temp then newtemp else t) dst
                            val newinstr =
                              case instr'
                                of Assem.OPER{assem,dst,src,jump} =>
                                    Assem.OPER{assem=assem, dst=newdst, src=src, jump=jump}
                                 | Assem.LABEL{assem,...} =>
                                    instr'
                                 | Assem.MOVE{assem,dst,src} =>
                                    Assem.MOVE{assem=assem, dst=newtemp, src=src}
                            val tree = Tree.MOVE(F.getAccess(access)(Tree.TEMP F.FP), Tree.TEMP newtemp)
                            val newinstrs = Amd64Codegen.codegen frame tree
                          in
                            instrs @ [newinstr] @ newinstrs
                          end
                        else
                          instrs @ [instr']
                      fun s() =
                        if List.exists (fn t => t = temp) src then
                          let
                            val newtemp = Temp.newTemp()
                            val newsrc = List.map (fn t => if t = temp then newtemp else t) src
                            val newinstr =
                              case instr
                                of Assem.OPER{assem,dst,src,jump} =>
                                    Assem.OPER{assem=assem, dst=dst, src=newsrc, jump=jump}
                                 | Assem.LABEL{assem,...} =>
                                    instr
                                 | Assem.MOVE{assem,dst,src} =>
                                    Assem.MOVE{assem=assem, dst=dst, src=newtemp}
                            val tree = Tree.MOVE(Tree.TEMP newtemp, F.getAccess(access)(Tree.TEMP F.FP))
                            val newinstrs = Amd64Codegen.codegen frame tree
                          in
                            (instrs @ newinstrs, newinstr)
                          end
                        else
                          (instrs, instr)
                    in
                      d(s())
                    end
                in
                  case instr
                    of Assem.OPER{assem,dst,src,jump} =>
                      foreach(dst, src)
                     | Assem.LABEL{assem,...} =>
                      instrs @ [instr]
                     | Assem.MOVE{assem,dst,src} =>
                      foreach([dst], [src])
                end
            in
              instructions := foldl iterInstructions nil (!instructions)
            end
          val newTemps = nodeSet.app foreachSpill (!spilledNodes)
        in
        (* TODO:
        * Allocate memory locations for each v in spilledNodes.
        * Create a new temporary vi for each definition and each use.
        * In the program (instructions), insert a store after each definition of a vi, a fetch before each use of a vi.
        * Put all the vi into a set newTemps.
        * *)
          spilledNodes := nodeSet.empty;
          initial := nodeSet.union(!coloredNodes, !coalescedNodes);
          coloredNodes := nodeSet.empty;
          coalescedNodes := nodeSet.empty;
          E.debug "exit rewriteProgram\n"
        end
    in
      main();
      (!instructions, !allocation')
    end
end

