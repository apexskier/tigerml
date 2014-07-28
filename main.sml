structure Main = struct

  structure Tr = Translate
  structure F = Amd64Frame
  (* structure R = RegAlloc *)

  fun getsome(SOME x) = x
    | getsome(NONE) = ErrorMsg.impossible "nothing found when getsome"

  fun emitproc out (F.PROC{body,frame}) =
        let
          val _ = print (Symbol.name(F.name frame) ^ ":\n")
          val _ = TextIO.output(out, Symbol.name(F.name frame) ^ ":\n")
          val stms = Canon.traceSchedule(Canon.basicBlocks(Canon.linearize body))
          val _ = app (fn s => Printtree.printtree(TextIO.stdOut, s)) stms
          val instrs = List.concat(map (Amd64Codegen.codegen frame) stms)
          val format0 = Assem.format(Temp.makeString)
        in
          app (fn i => TextIO.output(out, format0 i)) instrs;
          print "\n"
        end
    | emitproc out (F.STRING(lab,s)) =
        (TextIO.output(out, F.string(lab,s));
        print ((Symbol.name lab) ^ ": \"" ^ s ^ "\"\n");
        print "\n")

  fun withOpenFile fname f =
    let
      val out = TextIO.openOut fname
    in (f out before TextIO.closeOut out)
      handle e => (TextIO.closeOut out; raise e)
    end

  fun compile filename =
    let
      val absyn = Parse.parse filename
      val _ = print "\n## Type checking\n"
      val _ = Semant.transProg absyn
      val _ = print "\n## Abstract Syntax Tree\n"
      val _ = PrintAbsyn.print(TextIO.stdOut, absyn)
      val frags = Tr.getResult()
      val _ = print "\n## Tree\n"
    in
      withOpenFile (filename ^ ".s")
      (fn out => (app (emitproc out) frags))
    end

end



