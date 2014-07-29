structure Amd64Color : COLOR =
struct
  structure Frame = Amd64Frame
  structure T = Temp
  structure TT = Temp.Table
  structure F = Frame

  type allocation = F.register TT.table

  fun color{interference, initial, spillCost, registers} =
    (initial, nil)
end
