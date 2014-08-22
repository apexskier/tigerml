signature REGALLOC =
sig
  structure Frame : FRAME
  type allocation = Frame.register Temp.Table.table
  val alloc : Assem.instr list * Frame.frame * bool * bool * bool -> Assem.instr list * allocation
end
