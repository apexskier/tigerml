structure Main = struct
  structure Tr = Translate
  structure F = Amd64Frame
  (* structure R = RegAlloc *)

  fun getsome(SOME x) = x
    | getsome(NONE) = ErrorMsg.impossible "nothing found when getsome"

  fun emitproc out (F.PROC{body,frame}) =
        let
          val body' = F.procEntryExit1(frame, body)
          val _ = ErrorMsg.debug (Symbol.name(F.name frame) ^ ":\n")
          val _ = print "\n### Tree before canon\n"
          val _ = Printtree.printtree(TextIO.stdOut, body')
          val blocks = Canon.basicBlocks(Canon.linearize body')
          val stms = Canon.traceSchedule(blocks)
          val _ = print "\n### Tree after canon\n"
          val _ = app (fn s => Printtree.printtree(TextIO.stdOut, s)) stms

          val instrs = List.concat(map (Amd64Codegen.codegen frame) stms)

          val (instrs', allocation) = Amd64RegAlloc.alloc(instrs, frame)

          val {prolog, body=instrs'', epilog} = F.procEntryExit3(frame, instrs')

          fun format(t) =
            case Temp.Table.look(F.tempMap, t)
              of SOME(s) => "%" ^ s
               | NONE => Temp.makeString(t)

          fun allocFormat(t) =
            case Temp.Table.look(allocation, t)
              of SOME r => "%" ^ r
               | NONE => ErrorMsg.impossible ("no allocated register found for temp '" ^ format(t) ^ "'")

          val format0 = Assem.format(allocFormat)
        in
          TextIO.output(out, prolog);
          app (fn i => (
            TextIO.output(TextIO.stdOut, Assem.format(format) i);
            TextIO.output(out, format0 i))) instrs'';
          TextIO.output(out, epilog);
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
      val _ = print "\n## Abstract Syntax Tree\n"
      val _ = PrintAbsyn.print(TextIO.stdOut, absyn)
      val _ = print "\n## Type checking\n"
      val _ = Semant.transProg absyn
      val frags = Tr.getResult()
    in
      withOpenFile (filename ^ ".s")
      (fn out => (app (emitproc out) frags))
    end
end
