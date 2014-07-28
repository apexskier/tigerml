signature FRAME =
sig
  type frame
  type access
  type register = Temp.temp (* NOTE: in the book, this is a string *)
  val newFrame : {name: Temp.label, formals: bool list} -> frame
  val name : frame -> Temp.label
  val formals : frame -> access list
  val allocLocal : frame -> bool -> access

  datatype frag = PROC of {body: Tree.stm, frame: frame}
                | STRING of Temp.label * string

  val FP : register
  val RA : register
  val registers : string list
  val registerTemps : register list
  val wordsize : int
  val exp : access -> Tree.exp -> Tree.exp

  val externalCall : string * Tree.exp list -> Tree.exp
  val string : Temp.label * string -> string
  val tempMap : string Temp.Table.table

  (* private to all but amd64frame *)
  val callerSaves : register list
  val argRegs : register list
end
