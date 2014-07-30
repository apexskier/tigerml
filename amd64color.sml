structure Amd64Color : COLOR =
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
      val simplifyWorklist = nil:IG.node list (* Low-degree non-move-related nodes *)
      val freezeWorklist = nil:IG.node list (* Low-degree move-related nodes *)
      val spillWorklist = nil:IG.node list (* High-degree nodes *)
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
      val worklistMoves = nil:FG.node list (* moves enabled for possible coalescing *)
      val activeMoves = nil:FG.node list (* moves not yet ready for coalescing *)

      (* Other data structures *)
      val adjSet = nil
      val adjList = nil
      val degree = nil
      val moveList = nil
      val alias = nil
      val color = nil
    in
      (initial, nil)
    end
end
