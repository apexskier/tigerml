structure Color : COLOR =
struct
  structure Frame = Amd64Frame
  structure F = Frame
  structure T = Temp
  structure TT = Temp.Table

  structure FG = Flow.Graph
  structure IG = Liveness.IGraph

  type allocation = F.register TT.table

  fun color{interference, initial, spillCost, registers} =
    let
      (* Node work-lists, sets, and stacks.
      * The following lists and sets are always mutually disjoint and every
      * node is always in exactly one of the sets or lists. *)
      val precolored = nil:F.register list (* machine registers, preassigned a color *)
      val _ = initial (* temporary registers, not precolored and not yet processed *)
      val simplifyWorklist = ref nil:IG.node list (* Low-degree non-move-related nodes *)
      val freezeWorklist = ref nil:IG.node list (* Low-degree move-related nodes *)
      val spillWorklist = ref nil:IG.node list (* High-degree nodes *)
      val spilledNodes = nil:IG.node list (* nodes marked for spilling during this round; initially empty. *)
      val coalescedNodes = nil:F.register list (* registers that have been coalesced *)
      val coloredNodes = nil:IG.node list (* nodes successfully colored *)
      val selectStack = nil:T.temp list (* stack containing temporaries removed from the graph *)

      (* Move sets
      * There are five sets of move instructions, and every move is in exactly
      * one of these sets (after Build through the end of Main) *)
      val coalescedMoves = nil:FG.node list (* moves that have been coalesced *)
      val constrainedMoves = nil:FG.node list (* moves whose source and target interfere *)
      val frozenMoves = nil:FG.node list (* moves that will no longer be considered for coalescing *)
      val worklistMoves = ref nil:FG.node list (* moves enabled for possible coalescing *)
      val activeMoves = nil:FG.node list (* moves not yet ready for coalescing *)

      (* Other data structures *)
      val adjSet = nil
      val adjList = nil
      val degree = nil
      val moveList = nil
      val alias = nil
      val color = nil

      val k:int = 9

      fun main() =
        let
          fun repeat(simplifyWorklist, worklistMoves, freezeWorklist, spillWorklist) =
            if simplifyWorklist <> nil then repeat(simplify(simplifyWorklist, worklistMoves, freezeWorklist, spillWorklist))
            else if worklistMoves <> nil then repeat(coalesce(simplifyWorklist, worklistMoves, freezeWorklist, spillWorklist))
            else if freezeWorklist <> nil then repeat(freeze(simplifyWorklist, worklistMoves, freezeWorklist, spillWorklist))
            else if spillWorklist <> nil then repeat(selectSpill(simplifyWorklist, worklistMoves, freezeWorklist, spillCost))
            else (simplifyWorklist, worklistMoves, freezeWorklist, spillWorklist)
          val _ = livenessAnalysis()
          val _ = build()
          val _ = makeWorklist()
          val (simplifyWorklist, worklistMoves, freezeWorklist, spillWorklist) = repeat()
            val _ = if simplifyWorklist <> nil then ErrorMsg.impossible "simplifyWorklist not nil" else ()
            val _ = if worklistMoves <> nil then ErrorMsg.impossible "worklistMoves not nil" else ()
            val _ = if freezeWorklist <> nil then ErrorMsg.impossible "freezeWorklist not nil" else ()
            val _ = if spillWorklist <> nil then ErrorMsg.impossible "spillWorklist not nil" else ()
          val _ = assignColors()
        in
          if spilledNodes <> nil then
            (rewriteProgram(spilledNodes)
            main())
          else ()
        end

      and build() =
        let
          fun forall(b) =
            let
              val live = ref liveOut(b)
              fun forall'(i) =
                (if isMoveInstruction(i) then
                  let
                    val _ = live := without(live, use(i))
                    fun forall''(n) =
                      moveList[n] := union(moveList[n], [i])
                    val _ = app forall'' union(def(i), use(i))
                    val _ = worklistMoves := union(worklistMoves, [i])
                  in () end
                else ();
                app (fn d => app (fn l => addEdge(l, d)) !live) (def(i));
                live := union(use(i), not(live, def(i))))
            in app forall' (rev(instructions(b))) end
        in app forall (blocks(program)) end

      and addEdge(u, v) =
        if not(member((u, v), !adjSet)) andalso not(G.eq(u, v)) then
          (adjSet := union(!adjSet, [(u, v), (v, u)]);
          if not(member(u, precolored)) then
            (adjList[u] := union(adjList[u], [v])
            degree[u] := degree[u] + 1) else ();
          if not(member(v, precolored)) then
            (adjList[v] := union(adjList[v], [u])
            degree[v] := degree[v] + 1) else ())
        else ()

      and makeWorklist() =
        let
          fun forall(n) =
            (initial := without(initial, [n]);
            if degree(n) >= k then
              spillWorklist := union(spillWorklist, [n])
            else if moveRelated(n) then
              freezeWorklist := union(freezeWorklist, [n])
            else
              simplifyWorklist := union(simplifyWorklist, [n]))
        in
          app forall initial
        end

      and adjacent(n) =
        without(adjList(n), union(selectStack, coalescedNodes))

      and nodeMoves(n) =
        intersect(moveList[n], union(activeMoves, worklistMoves))

      and moveRelated(n):bool =
        nodeMoves(n) <> nil

      and simplify() =
        let
          val n = pop(simplifyWorklist)
          val _ = without(simplifyWorklist, [n])
          val _ = push(n, selectStack)
        in
          app decrementDegree (adjacent(n))
        end

      and decrementDegree(m) =
        let
          val d = degree(m)
          val _ = degree(m) := d - 1
        in
          if d = k then
            (enableMoves(union([m], adjacent(m)));
            spillWorklist := without(spillWorklist, [m]);
            if moveRelated(m) then
              freezeWorklist := union(freezeWorklist, [m])
            else
              simplifyWorklist := union(simplifyWorklist, [m]))
          else ()
        end

      and enableMoves(nodes) =
        let
          fun forall(n) =
            let
              fun forall'(m) =
                if member(m, activeMoves) then
                  (activeMoves := without(activeMoves, [m]);
                  worklistMoves := union(worklistMoves, [m]))
                else ()
            in
              app forall' (nodeMoves(n))
            end
        in app forall nodes end

      and coalesce() =
        let
          val m = hd worklistMoves
          val x = getAlias(#1 m)
          val y = getAlias(#2 m)
          val (u, v) =
            if member(y, precolored) then
              (y, x)
            else
              (x, y)
        in
          (worklistMoves := without(worklistMoves, [m]);
          if eq(u, v) then
            (coalescedMoves := union(coalescedMoves, [m]);
            addWorkList(u))
          else if member(v, precolored) andalso member((u, v), adjSet) then
            (constrainedMoves := union(constrainedMoves, [m]);
            addWorkList(u); addWorkList(v))
          else if (member(u, precolored) andalso (List.all (fn t => ok(t, u)) (adjacent(v)))) or (not(member(u, precolored)) andalso conservative(union(adjacent(u), adjacent(v)))) then
            (coalescedMoves := union(coalescedMoves, [m]);
            combine(u, v)
            addWorkList(u))
          else activeMoves := union(activeMoves, [m]))
        end

      and addWorkList(u) =
        if not(member(u, precolored)) andalso not(moveRelated(u)) andalso degree(u) < k then
          (freezeWorklist := without(freezeWorklist, [u]);
          simplifyWorklist := union(simplifyWorklist, [u]))
        else ()

      and ok(t, r) =
        degree(t) < k or member(t, precolored) or member((t, r), adjSet)

      and conservative(nodes) =
        let
          val k' = ref 0
          fun forall(n) =
            if degree(n) >= !k then k' := !k' + 1 else ()
        in
          (app forall nodes;
          k' < k)
        end

      and getAlias(n) =
        if member(n, coalescedNodes) then
          getAlias(alias[n])
        else n

      and combine(v, u) =
        (if member(v, freezeWorklist) then
          freezeWorklist := without(freezeWorklist, [v])
        else
          spillWorklist := without(spillWorklist, [v]);
        coalescedNodes := union(coalescedNodes, [v]);
        alias[v] := u;
        moveList[u] := union(moveList[u], moveList[v]);
        enableMoves(v);
        app (fn t => (addEdge(t, u); decrementDegree(t))) adjacent(v);
        if degree(u) >= k andalso member(u, freezeWorklist) then
          (freezeWorklist := without(freezeWorklist, [u]);
          spillWorklist := union(spillWorklist, [u]))
        else ())

      and freeze() =
        let
          val u = pop(freezeWorklist)
        in
          freezeWorklist := without(freezeWorklist, [u]);
          simplifyWorklist := union(simplifyWorklist, [u]);
          freezeMoves(u)
        end

      and freezeMoves(u) =
        let
          fun forall(m as (x, y)) =
            let
              val v =
                if getAlias(y) = getAlias(u) then
                  getAlias(x)
                else
                  getAlias(y)
            in
              activeMoves := without(activeMoves, [m]);
              frozenMoves := union(frozenMoves, [m]);
              if (nodeMoves(v) = nil andalso degree(v) < k) then
                (freezeWorklist := without(freezeWorklist, [v]);
                simplifyWorklist := union(simplifyWorklist, [v]))
              else ()
            end
        in
          app forall (nodeMoves(u))
        end

      and selectSpill() =
        let
          val m = hd spillWorklist (* from book:
                                     * "select using favoriate heuristic. Note: avoid choosing nodes that
                                     * are the tiny live ranges resulting from the fetches of previously
                                     * spilled registers" *)
        in
          spillWorklist := without(spillWorklist, [m]);
          simplifyWorklist := union(simplifyWorklist, [m]);
          freezeMoves(m)
        end

      and assignColors() =
        (while !selectStack <> nil do
          let
            val n = pop(selectStack)
            val i = ref 0
            val okColors = ref (map (fn x=>x-1) List.tabulate(k, fn x => x+1))
            fun forall(w) =
              if member(getAlias(w), (union(coloredNodes, precolored))) then
                okColors := without(okColors, [color(getAlias(w))])
              else ()
          in
            app forall adjList(n);
            if okColors = nil then
              spilledNodes := union(spilledNodes, [n])
            else
              (coloredNodes := union(coloredNodes, [n]);
              let
                val c = hd okColors
              in color[n] := c end)
          end;
        app (fn n => color[n] := color[getAlias(n)]) coalescedNodes)

      and rewriteProgram() =
        (*
        * Allocate memory locations for each v in spilledNodes.
        * Create a new temporary vi for each definition and each use.
        * In the program (instructions), insert a store after each definition of a vi, a fetch before each use of a vi.
        * Put all the vi into a set newTemps.
        * *)
        (spilledNodes := nil;
        initial := union(coloredNodes, union(coalescedNodes, newTemps));
        coloredNodes := nil;
        coalescedNodes := nil)

    in
      main()
    end
end
