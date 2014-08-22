structure Main = struct
  structure Tr = Translate
  structure F = Amd64Frame
  (* structure R = RegAlloc *)

  fun getsome(SOME x) = x
    | getsome(NONE) = ErrorMsg.impossible "nothing found when getsome"

  fun emitproc(out, prtree, prcanontree, _, prcfgraph, prigraph, prliveout) (F.PROC{body,frame}) =
        let
          val body' = F.procEntryExit1(frame, body)
          val blocks = Canon.basicBlocks(Canon.linearize body')
          val stms = Canon.traceSchedule(blocks)

          val _ =
            if prtree then
              (print(Symbol.name(F.name frame) ^ ":\n");
              Printtree.printtree(TextIO.stdOut, body'))
            else ()
          val _ =
            if prcanontree then
              (print(Symbol.name(F.name frame) ^ ":\n");
              app (fn s => Printtree.printtree(TextIO.stdOut, s)) stms)
            else ()

          val instrs = List.concat(map (Amd64Codegen.codegen frame) stms)

          val (instrs', allocation) = Amd64RegAlloc.alloc(instrs, frame, prcfgraph, prigraph, prliveout)

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
          app (fn i => (TextIO.output(out, format0 i))) instrs'';
          TextIO.output(out, epilog)
        end
    | emitproc(out, _, _, prstrings, _, _, _) (F.STRING(lab,s)) =
        (TextIO.output(out, F.string(lab,s));
        if prstrings then
          print ((Symbol.name lab) ^ ": \"" ^ s ^ "\"\n")
        else ())

  fun withOpenFile fname f =
    let
      val out = TextIO.openOut fname
    in (f out before TextIO.closeOut out)
      handle e => (TextIO.closeOut out; raise e)
    end

  fun compile(filename, prabsyn, prtree, prcanontree, prstrings, prcfgraph, prigraph, prliveout) =
    let
      val absyn = Parse.parse filename
      val _ = Semant.transProg absyn
      val frags = Tr.getResult()
    in
      if prabsyn then
        PrintAbsyn.print(TextIO.stdOut, absyn)
      else ();
      withOpenFile (filename ^ ".s")
        (fn out => (app (emitproc(out, prtree, prcanontree, prstrings, prcfgraph, prigraph, prliveout)) frags))
    end
end
