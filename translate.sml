signature TRANSLATE =
sig
  type level
  type access (* not the same as FRAME.access *)

  structure Frame : FRAME

  val outermost : level
  val newLevel : {parent:level, name:Temp.label, formals:bool list} -> level
  val formals : level -> Frame.access list
  val allocLocal : level -> bool -> access
end

structure Translate : TRANSLATE =
struct
  structure Frame = Amd64Frame

  datatype level = Outer
                 | Level of {frame:Frame.frame, parent:level}
  type access = level * Frame.access

  val outermost = Outer

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
end
