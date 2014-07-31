structure Color : COLOR =
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

  fun color{interference as Liveness.IGRAPH{graph, tnode, gtemp, moves}, initial:allocation, spillCost, registers} =
    (initial, nil:Temp.temp list)
end
