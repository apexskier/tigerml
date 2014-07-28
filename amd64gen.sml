structure Amd64Codegen : CODEGEN =
struct
  structure Frame = Amd64Frame
  structure A = Assem
  structure T = Tree

  fun codegen(frame)(stm:Tree.stm):Assem.instr list =
    let
      val ilist = ref (nil:A.instr list)
      fun emit x = ilist := x :: !ilist
      fun result(gen) =
        let
          val t = Temp.newTemp()
        in
          gen t;
          t
        end

      fun munchStm(_) =
        ()
      and munchExp(_) =
        ()
    in
      munchStm stm;
      rev(!ilist)
    end
end
