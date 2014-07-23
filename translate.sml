signature TRANSLATE =
sig
  type level
  type access (* not the same as FRAME.access *)
  type exp

  structure Frame : FRAME

  val outermost : level
  val fragments : Frame.frag list ref

  val newLevel : {parent:level, name:Temp.label, formals:bool list} -> level
  val formals : level -> Frame.access list
  val allocLocal : level -> bool -> access

  val procEntryExit : {level:level, body:exp} -> unit
  val getResult : unit -> Frame.frag list
end

structure Translate : TRANSLATE =
struct
  structure Frame = Amd64Frame

  datatype level = Outer
                 | Level of {frame:Frame.frame, parent:level}
  type access = level * Frame.access
  datatype exp = Ex of Tree.exp                            (* expression with result *)
               | Nx of Tree.stm                            (* no result *)
               | Cx of Temp.label * Temp.label -> Tree.stm (* conditional *)

  val outermost = Outer
  val fragments = ref(nil:Frame.frag list)

  fun newLevel{parent, name, formals} =
    (* create a new frame, inserting an extra parameter for the static link *)
    Level{frame=Frame.newFrame({name=name, formals=true :: formals}), parent=parent}

  fun formals(level) =
    case level
      of Outer => []
       | Level{frame, parent} =>
        Frame.formals(frame)

  fun allocLocal(level) =
    case level
      of Outer =>
        raise Fail "Allocating locals at outermost level"
       | Level{frame, parent} =>
        (fn(g) =>
          (level, Frame.allocLocal(frame)(g)))

  fun procEntryExit{level, body} =
    ()

  fun getResult() = !fragments
end
