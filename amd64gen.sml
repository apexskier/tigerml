structure Amd64Codegen : CODEGEN =
struct
  structure Frame = Amd64Frame
  structure F = Frame
  structure A = Assem
  structure S = Symbol
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

      fun intStr(i) =
        if i <> 0 then Int.toString i
        else ""

      fun assemOperJmp(oper) =
        (case oper
          of T.EQ => "je"
           | T.NE => "je"
           | T.LT => "jl"
           | T.GT => "jg"
           | T.LE => "jle"
           | T.GE => "jge"
           | T.ULT => "jb"
           | T.ULE => "jbe"
           | T.UGT => "ja"
           | T.UGE => "jae")

      fun assemOper(oper) =
        (case oper
          of T.PLUS => "addq"
           | T.MINUS => "subq"
           | T.MUL => "imulq"
           | T.DIV => "idivq"
           | T.AND => "andq"
           | T.OR => "orq"
           | T.LSHIFT => "shlq"
           | T.RSHIFT => "shrq"
           | T.ARSHIFT => "sarq"
           | T.XOR => "xor")

      fun munchStm(T.SEQ(a, b)) =
            (munchStm a; munchStm b)

        | munchStm(T.LABEL l) =
            emit(A.LABEL{assem=S.name l ^ ":\n", lab=l})

        | munchStm(T.JUMP(T.NAME lab, labs)) =
            emit(A.OPER{assem="jmp " ^ S.name lab ^ "\n",
                        src=nil,
                        dst=nil,
                        jump=SOME labs})
        | munchStm(T.JUMP(e, labs)) =
            let
              val e' = munchExp e
            in
              emit(A.OPER{assem="jmp `s0\n",
                          src=[e'],
                          dst=nil,
                          jump=SOME labs})
            end

        | munchStm(T.CJUMP(oper, T.CONST i, e, l1, l2)) =
            emit(A.OPER{assem="cmp `s0, $" ^ Int.toString i ^ "\n" ^
                              assemOperJmp oper ^ " " ^
                              (if oper = T.NE then S.name l2 else S.name l1) ^ "\n",
                        src=[munchExp e],
                        dst=nil,
                        jump=SOME[l1, l2]})
        | munchStm(T.CJUMP(oper, e, T.CONST i, l1, l2)) =
            emit(A.OPER{assem="cmp $" ^ Int.toString i ^ ", `s0\n" ^
                              assemOperJmp oper ^ " " ^
                              (if oper = T.NE then S.name l2 else S.name l1) ^ "\n",
                        src=[munchExp e],
                        dst=nil,
                        jump=SOME[l1, l2]})
        | munchStm(T.CJUMP(oper, e1, e2, l1, l2)) =
            emit(A.OPER{assem="cmp `s1, `s0\n" ^
                              assemOperJmp oper ^ " " ^
                              (if oper = T.NE then S.name l2 else S.name l1) ^ "\n",
                        src=[munchExp e1, munchExp e2],
                        dst=nil,
                        jump=SOME[l1, l2]})

        | munchStm(T.MOVE(T.TEMP t0, T.TEMP t1)) =
            emit(A.MOVE{assem="movq `s0, `d0\n",
                        src=t1,
                        dst=t0})
        | munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS, T.TEMP t, T.CONST i)), T.CONST j)) =
            emit(A.OPER{assem="movq $" ^ Int.toString j ^ ", " ^ intStr i ^ "(`d0)\n",
                        src=nil,
                        dst=[t],
                        jump=NONE})
        | munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS, T.TEMP t, T.CONST i)), T.NAME n)) =
            emit(A.OPER{assem="movq $" ^ S.name n ^ ", " ^ intStr i ^ "(`d0)\n",
                        src=nil,
                        dst=[t],
                        jump=NONE})
        | munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS, T.TEMP t, T.CONST i)), e)) =
            emit(A.OPER{assem="movq `s0, " ^ intStr i ^ "(`d0)\n",
                        src=[munchExp e],
                        dst=[t],
                        jump=NONE})
        | munchStm(T.MOVE(T.MEM(T.TEMP t0), T.TEMP t1)) =
            emit(A.OPER{assem="movq `s0, (`d0)\n",
                        src=[t1], dst=[t0], jump=NONE})
        | munchStm(T.MOVE(T.TEMP t0, T.MEM(T.TEMP t1))) =
            emit(A.OPER{assem="movq (`s0), `d0\n",
                        src=[t1], dst=[t0], jump=NONE})
        | munchStm(T.MOVE(T.TEMP t0, T.BINOP(oper, T.CONST i, T.TEMP t1))) =
            if t1 = t0 then
              emit(A.OPER{assem=assemOper oper ^ " $" ^ Int.toString i ^ ", `s0 # coalescing a temp to const + temp instruction\n",
                          src=[t0, t1], dst=[t0], jump=NONE})
            else
              (emit(A.MOVE{assem="movq `s0, `d0\n",
                          src=t1, dst=t0});
              emit(A.OPER{assem=assemOper oper ^ " $" ^ Int.toString i ^ ", `d0\n",
                          src=[], dst=[t0], jump=NONE}))
        | munchStm(T.MOVE(T.TEMP t0, T.BINOP(oper, T.TEMP t1, T.CONST i))) =
            if t1 = t0 then
              emit(A.OPER{assem=assemOper oper ^ " $" ^ Int.toString i ^ ", `s0 # coalescing a temp to temp + const instruction\n",
                          src=[t0, t1], dst=[t0], jump=NONE})
            else
              (emit(A.MOVE{assem="movq `s0, `d0\n",
                          src=t1, dst=t0});
              emit(A.OPER{assem=assemOper oper ^ " $" ^ Int.toString i ^ ", `d0\n",
                          src=[], dst=[t0], jump=NONE}))
        | munchStm(T.MOVE(T.TEMP t0, T.BINOP(oper, T.TEMP t1, T.TEMP t2))) =
            if t0 = t1 then
              emit(A.OPER{assem=assemOper oper ^ " `s1, `d0 # coalescing a temp to temp + temp instruction\n",
                          src=[t0, t2], dst=[t0], jump=NONE})
            else
              if t0 = t2 then
                emit(A.OPER{assem=assemOper oper ^ " `s1, `d0 # coalescing a temp to temp + temp instruction\n",
                            src=[t0, t1], dst=[t0], jump=NONE})
              else
                (emit(A.MOVE{assem="movq `s0, `d0\n",
                            src=t1, dst=t0});
                emit(A.OPER{assem=assemOper oper ^ " `s1, `d0\n",
                            src=[t2], dst=[t0], jump=NONE}))
        | munchStm(T.MOVE(T.TEMP t, T.CONST i)) =
            emit(A.OPER{assem="movq $" ^ Int.toString i ^ ", `d0\n",
                        src=nil,
                        dst=[t],
                        jump=NONE})
        | munchStm(T.MOVE(T.TEMP t, e)) =
            emit(A.MOVE{assem="movq `s0, `d0\n",
                        src=munchExp e,
                        dst=t})

        | munchStm(T.EXP e) =
            (munchExp e; ())

        | munchStm tree =
            (print "buggy tree:\n"; Printtree.printtree(TextIO.stdOut, tree);
            ErrorMsg.impossible "unexpected statement in maximal munch algorithm")

      and munchArgs(argnum, arg::args) =
            let
              val arg' = munchExp arg
            in
              emit(A.MOVE{assem="movq `s0, `d0\n",
                         src=arg', dst=List.nth(F.argRegs, argnum)});
              arg' :: munchArgs(argnum + 1, args)
            end
        | munchArgs(argnum, []) = []

      and munchExp(T.BINOP(oper, e1, e2)) = (* TODO: multiply needs to be written, as it does some crazy stuff with other registers *)
            result(fn r => (emit(A.MOVE{assem="movq `s0, `d0\n",
                                       src=munchExp e1, dst=r});
                           emit(A.MOVE{assem=assemOper oper ^ " `s0, `d0\n",
                                       src=munchExp e2, dst=r})))

        | munchExp(T.MEM(T.BINOP(T.PLUS, e, T.CONST i))) =
            result(fn r => emit(A.MOVE{assem="movq " ^ intStr i ^ "(`s0), `d0\n",
                                       src=munchExp e, dst=r}))
        | munchExp(T.MEM(T.BINOP(T.PLUS, T.CONST i, e))) =
            result(fn r => emit(A.MOVE{assem="movq " ^ intStr i ^ "(`s0), `d0\n",
                                       src=munchExp e, dst=r}))
        | munchExp(T.MEM(e)) =
            result(fn r => emit(A.MOVE{assem="movq (`s0), `d0\n",
                                       src=munchExp e, dst=r}))

        | munchExp(T.TEMP t) =
            t

        | munchExp(T.ESEQ(s, e)) =
            (munchStm s;
            munchExp e)

        | munchExp(T.NAME n) =
            result(fn r => emit(A.OPER{assem="movq $" ^ S.name n ^ ", `d0\n",
                                       src=nil, dst=[r], jump=NONE}))

        | munchExp(T.CONST i) =
            result(fn r => emit(A.OPER{assem="movq $" ^ Int.toString i ^ ", `d0\n",
                                       src=nil, dst=[r], jump=NONE}))

        | munchExp(T.CALL(T.NAME n, args)) =
            (result(fn r => emit(A.OPER{assem="call " ^ S.name n ^ "\n",
                                       src=munchArgs(0, args),
                                       dst=F.callerSaves, jump=NONE}));
            F.RV)
        | munchExp(T.CALL(e, args)) =
            let
              val e' = munchExp e
            in
              result(fn r => emit(A.OPER{assem="call *`s0\n",
                                         src=munchExp e :: munchArgs(0, args),
                                         dst=F.callerSaves, jump=NONE}));
              F.RV
            end

    in
      munchStm stm;
      rev(!ilist)
    end
end
