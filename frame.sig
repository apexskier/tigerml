signature FRAME =
sig
  type frame
  type access
  type register = string
  val newFrame : {name: Temp.label, formals: bool list, argspace: int} -> frame
  val name : frame -> Temp.label
  val formals : frame -> access list
  val allocLocal : frame -> bool -> access

  datatype frag = PROC of {body: Tree.stm, frame: frame}
                | STRING of Temp.label * string

  val FP : Temp.temp
  val RV : Temp.temp
  val DivReg : Temp.temp
  val registers : string list
  val registerTemps : Temp.temp list
  val wordsize : int
  val getAccess : access -> Tree.exp -> Tree.exp

  val externalCall : string * Tree.exp list -> Tree.exp
  val string : Temp.label * string -> string
  val tempMap : register Temp.Table.table

  val procEntryExit1 : frame * Tree.stm -> Tree.stm
  val procEntryExit2 : frame * Assem.instr list -> Assem.instr list
  val procEntryExit3 : frame * Assem.instr list -> {prolog:string,
                                                    body:Assem.instr list,
                                                    epilog:string}

  (* private to all but amd64frame *)
  val callerSaves : Temp.temp list
  val calleeSaves : Temp.temp list
  val argRegs : Temp.temp list
  val colorables : Temp.temp list
end
