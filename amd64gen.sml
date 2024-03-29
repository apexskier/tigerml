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
           | T.NE => "jne"
           | T.LT => "jl"
           | T.GT => "jg"
           | T.LE => "jle"
           | T.GE => "jge"
           | T.ULT => "jb"
           | T.ULE => "jbe"
           | T.UGT => "ja"
           | T.UGE => "jae")
      fun assemOperRev(oper) =
        (case oper (* TODO: Test these *)
          of T.EQ => T.NE
           | T.NE => T.EQ
           | T.LT => T.GE
           | T.GT => T.LE
           | T.LE => T.GT
           | T.GE => T.LT
           | T.ULT => T.UGT
           | T.ULE => T.UGE
           | T.UGT => T.ULE
           | T.UGE => T.ULT)

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
            emit(A.OPER{assem="jmp \t" ^ S.name lab ^ "\n",
                        src=nil,
                        dst=nil,
                        jump=SOME labs})
        | munchStm(T.JUMP(e, labs)) =
            let
              val e' = munchExp e
            in
              emit(A.OPER{assem="jmp \t`s0\n",
                          src=[e'],
                          dst=nil,
                          jump=SOME labs})
            end

        | munchStm(T.CJUMP(oper, T.CONST i, e, l1, l2)) =
            (emit(A.OPER{assem="cmp \t$" ^ Int.toString i ^ ", `s0\n",
                        src=[munchExp e],
                        dst=nil,
                        jump=NONE});
            emit(A.OPER{assem=assemOperJmp(assemOperRev oper) ^ " " ^ S.name l1 ^ "\n",
                        src=nil, dst=nil, jump=SOME[l1, l2]}))
        | munchStm(T.CJUMP(oper, e, T.CONST i, l1, l2)) =
            (emit(A.OPER{assem="cmp \t$" ^ Int.toString i ^ ", `s0\n",
                        src=[munchExp e],
                        dst=nil,
                        jump=NONE});
            emit(A.OPER{assem=assemOperJmp oper ^ " " ^ S.name l1 ^ "\n",
                        src=nil, dst=nil, jump=SOME[l1, l2]}))
        | munchStm(T.CJUMP(oper, e1, e2, l1, l2)) =
            (emit(A.OPER{assem="cmp \t`s1, `s0\n",
                        src=[munchExp e1, munchExp e2],
                        dst=nil,
                        jump=NONE});
            emit(A.OPER{assem=assemOperJmp oper ^ " " ^ S.name l1 ^ "\n",
                        src=nil, dst=nil, jump=SOME[l1, l2]}))

        | munchStm(T.MOVE(T.TEMP t0, T.TEMP t1)) =
            if t0 <> t1 then
              emit(A.MOVE{assem="movq \t`s0, `d0 \t# skipped a step\n",
                          src=t1,
                          dst=t0})
            else () (* NOTE: skipping move as args are the same *)
        | munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS, T.CONST i, T.TEMP t)), T.CONST j)) =
            emit(A.OPER{assem="movq \t$" ^ Int.toString j ^ ", " ^ intStr i ^ "(`s0)\n",
                        src=[t],
                        dst=nil,
                        jump=NONE})
        | munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS, T.TEMP t, T.CONST i)), T.CONST j)) =
            emit(A.OPER{assem="movq \t$" ^ Int.toString j ^ ", " ^ intStr i ^ "(`s0)\n",
                        src=[t],
                        dst=nil,
                        jump=NONE})
        | munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS, T.CONST i, e)), T.CONST j)) =
            emit(A.OPER{assem="movq \t$" ^ Int.toString j ^ ", " ^ intStr i ^ "(`s0)\n",
                        src=[munchExp e],
                        dst=nil,
                        jump=NONE})
        | munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS, e, T.CONST i)), T.CONST j)) =
            emit(A.OPER{assem="movq \t$" ^ Int.toString j ^ ", " ^ intStr i ^ "(`s0)\n",
                        src=[munchExp e],
                        dst=nil,
                        jump=NONE})
        | munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS, T.CONST i, T.TEMP t)), T.NAME n)) =
            emit(A.OPER{assem="movq \t$" ^ S.name n ^ ", " ^ intStr i ^ "(`s0)\n",
                        src=[t],
                        dst=nil,
                        jump=NONE})
        | munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS, T.TEMP t, T.CONST i)), T.NAME n)) =
            emit(A.OPER{assem="movq \t$" ^ S.name n ^ ", " ^ intStr i ^ "(`s0)\n",
                        src=[t],
                        dst=nil,
                        jump=NONE})
        | munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS, T.CONST i, e)), T.NAME n)) =
            emit(A.OPER{assem="movq \t$" ^ S.name n ^ ", " ^ intStr i ^ "(`s0)\n",
                        src=[munchExp e],
                        dst=nil,
                        jump=NONE})
        | munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS, e, T.CONST i)), T.NAME n)) =
            emit(A.OPER{assem="movq \t$" ^ S.name n ^ ", " ^ intStr i ^ "(`s0)\n",
                        src=[munchExp e],
                        dst=nil,
                        jump=NONE})
        | munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS, T.CONST i, T.TEMP t)), T.TEMP n)) =
            emit(A.OPER{assem="movq \t`s0, " ^ intStr i ^ "(`s1)\n",
                        src=[n, t],
                        dst=[],
                        jump=NONE})
        | munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS, T.TEMP t, T.CONST i)), T.TEMP n)) =
            emit(A.OPER{assem="movq \t`s0, " ^ intStr i ^ "(`s1)\n",
                        src=[n, t],
                        dst=[],
                        jump=NONE})
        | munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS, T.CONST i, e)), T.TEMP n)) =
            emit(A.OPER{assem="movq \t`s0, " ^ intStr i ^ "(`s1)\n",
                        src=[n, munchExp e],
                        dst=[],
                        jump=NONE})
        | munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS, e, T.CONST i)), T.TEMP n)) =
            emit(A.OPER{assem="movq \t`s0, " ^ intStr i ^ "(`s1)\n",
                        src=[n, munchExp e],
                        dst=[],
                        jump=NONE})
        | munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS, T.TEMP t, T.CONST i)), e)) =
            emit(A.OPER{assem="movq \t`s0, " ^ intStr i ^ "(`s1)\n",
                        src=[munchExp e, t],
                        dst=[],
                        jump=NONE})
        | munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS, T.CONST i, T.TEMP t)), e)) =
            emit(A.OPER{assem="movq \t`s0, " ^ intStr i ^ "(`s1)\n",
                        src=[munchExp e, t],
                        dst=[],
                        jump=NONE})
        | munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS, e1, T.CONST i)), e2)) =
            emit(A.OPER{assem="movq \t`s0, " ^ intStr i ^ "(`s1)\n",
                        src=[munchExp e2, munchExp e1],
                        dst=[],
                        jump=NONE})
        | munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS, T.CONST i, e1)), e2)) =
            emit(A.OPER{assem="movq \t`s0, " ^ intStr i ^ "(`s1)\n",
                        src=[munchExp e2, munchExp e1],
                        dst=[],
                        jump=NONE})
        | munchStm(T.MOVE(T.MEM(T.TEMP t0), T.TEMP t1)) =
            emit(A.OPER{assem="movq \t`s0, (`d0)\n",
                        src=[t1, t0], dst=[t0], jump=NONE})
        | munchStm(T.MOVE(T.MEM(T.TEMP t), T.CONST i)) =
            emit(A.OPER{assem="movq \t$" ^ Int.toString i ^ ", (`s0)\n",
                        src=[t], dst=nil, jump=NONE})
        | munchStm(T.MOVE(T.MEM(T.NAME n), e)) =
            ErrorMsg.impossible "tiger doesn't support direct memory access (from name)"
        | munchStm(T.MOVE(T.MEM(T.CONST i), e)) =
            ErrorMsg.impossible "tiger doesn't support direct memory access"
        | munchStm(T.MOVE(T.MEM e1, e2)) =
            emit(A.OPER{assem="movq \t`s0, (`s1)\n",
                        src=[munchExp e2, munchExp e1], dst=[], jump=NONE}) (* TODO: This is weird *)
        | munchStm(T.MOVE(T.CONST j, T.MEM e)) =
            ErrorMsg.impossible "moving memory into constant"
        | munchStm(T.MOVE(T.NAME n, T.MEM e)) =
            ErrorMsg.impossible "moving memory into name"
        | munchStm(T.MOVE(T.TEMP n, T.MEM(T.BINOP(T.PLUS, T.CONST i, T.TEMP t)))) =
            emit(A.OPER{assem="movq \t" ^ intStr i ^ "(`s0), `d0\n",
                        src=[t],
                        dst=[n],
                        jump=NONE})
        | munchStm(T.MOVE(T.TEMP n, T.MEM(T.BINOP(T.PLUS, T.TEMP t, T.CONST i)))) =
            emit(A.OPER{assem="movq \t" ^ intStr i ^ "(`s0), `d0\n",
                        src=[t],
                        dst=[n],
                        jump=NONE})
        | munchStm(T.MOVE(e, T.MEM(T.BINOP(T.PLUS, T.TEMP t, T.CONST i)))) =
            emit(A.OPER{assem="movq \t" ^ intStr i ^ "(`s0), `d0\n",
                        src=[t],
                        dst=[munchExp e],
                        jump=NONE})
        | munchStm(T.MOVE(e, T.MEM(T.BINOP(T.PLUS, T.CONST i, T.TEMP t)))) =
            emit(A.OPER{assem="movq \t" ^ intStr i ^ "(`s0), `d0\n",
                        src=[t],
                        dst=[munchExp e],
                        jump=NONE})
        | munchStm(T.MOVE(T.TEMP t0, T.MEM(T.TEMP t1))) =
            emit(A.OPER{assem="movq \t(`s0), `d0\n",
                        src=[t1], dst=[t0], jump=NONE})
        | munchStm(T.MOVE(T.TEMP t, T.MEM e)) =
            emit(A.OPER{assem="movq \t(`s0), `d0\n",
                        src=[munchExp e], dst=[t], jump=NONE})
        | munchStm(T.MOVE(e1, T.MEM e2)) =
            emit(A.OPER{assem="movq \t(`s0), `d0\t#testing \n",
                        src=[munchExp e2], dst=[munchExp e1], jump=NONE})
        | munchStm(T.MOVE(T.TEMP t0, T.BINOP(oper, T.CONST i, T.TEMP t1))) =
            (case oper
              of T.DIV =>
                ErrorMsg.impossible "not implemented" (* munchDiv() *)
               | _ =>
                if t1 = t0 then
                  emit(A.OPER{assem=assemOper oper ^ " \t$" ^ Int.toString i ^ ", `s0 \t# coalescing a temp to temp + const instruction\n",
                              src=[t0, t1], dst=[t0], jump=NONE})
                else
                  (emit(A.MOVE{assem="movq \t`s0, `d0\n",
                              src=t1, dst=t0});
                  emit(A.OPER{assem=assemOper oper ^ " \t$" ^ Int.toString i ^ ", `d0\n",
                              src=[t0], dst=[t0], jump=NONE})))
        | munchStm(T.MOVE(T.TEMP t, T.CONST i)) =
            emit(A.OPER{assem="movq \t$" ^ Int.toString i ^ ", `d0\n",
                        src=nil,
                        dst=[t],
                        jump=NONE})
        | munchStm(T.MOVE(T.TEMP t, e)) =
            emit(A.MOVE{assem="movq \t`s0, `d0\n",
                        src=munchExp e,
                        dst=t})
        | munchStm(T.MOVE(e1, e2)) =
            emit(A.OPER{assem="movq \t`s0, `d0\n",
                        src=[munchExp e2], dst=[munchExp e1], jump=NONE})

        | munchStm(T.EXP e) =
            (munchExp e; ())

        (* DEBUG: | munchStm tree =
            (print "buggy tree:\n"; Printtree.printtree(TextIO.stdOut, tree);
            ErrorMsg.impossible "unexpected statement in maximal munch algorithm") *)

      and munchArgs(argnum, arg::args) = (* TODO: handle more parameters than arg registers *)
            let
              val numRegs = length F.argRegs
              val arg' =
                if argnum < length F.argRegs then
                  List.nth(F.argRegs, argnum)
                else
                  F.FP
            in
              if argnum < length F.argRegs then
                (emit(A.MOVE{assem="movq \t`s0, `d0 \t# arg " ^ Int.toString argnum ^ "\n",
                            src=munchExp arg, dst=arg'});
                arg' :: munchArgs(argnum + 1, args))
              else
                (emit(A.OPER{assem="movq \t`s0, " ^ intStr((argnum - numRegs + 1) * F.wordsize) ^ "(`d0) \t# arg " ^ Int.toString argnum ^ "\n",
                            src=[munchExp arg], dst=[arg'], jump=NONE});
                arg' :: munchArgs(argnum + 1, args))
            end
        | munchArgs(argnum, []) = []

      and munchDiv(left, right) =
        (emit(A.OPER{assem="sar \t$63, `d0 \t# fill %rdx with the appropriate sign bit\n",
                     src=[], dst=[F.DivReg], jump=NONE});
        emit(A.MOVE{assem="mov \t`s0, `d0 \t# copy dividend into rax\n",
                    src=munchExp left, dst=F.RV});
        emit(A.OPER{assem="idiv \t`s0 \t\t# quotient in rax\n",
                    src=[munchExp right, F.RV], dst=[F.RV, F.DivReg], jump=NONE});
        F.RV)

      and munchExp(T.BINOP(oper, e1, e2)) =
            result(fn r =>
              (case oper
                of T.DIV =>
                    emit(A.MOVE{assem="movq \t`s0, `d0\n",
                                src=munchDiv(e1, e2), dst=r})
                 | _ =>
                  let
                    val e1' = munchExp e1
                    val e2' = munchExp e2
                  in
                    (emit(A.MOVE{assem="movq \t`s0, `d0\n",
                                                src=e1', dst=r});
                     emit(A.OPER{assem=assemOper oper ^ " \t`s0, `d0\n",
                                  src=[e2', e1'], dst=[r], jump=NONE}))
                  end))

        | munchExp(T.MEM(T.BINOP(T.PLUS, e, T.CONST i))) =
            result(fn r => emit(A.OPER{assem="movq \t" ^ intStr i ^ "(`s0), `d0 \t# mem exp\n",
                                       src=[munchExp e], dst=[r], jump=NONE}))
        | munchExp(T.MEM(T.BINOP(T.PLUS, T.CONST i, e))) =
            result(fn r => emit(A.OPER{assem="movq \t" ^ intStr i ^ "(`s0), `d0 \t# mem exp\n",
                                       src=[munchExp e], dst=[r], jump=NONE}))
        | munchExp(T.MEM e) =
            result(fn r => emit(A.OPER{assem=if true then "movq \t(`s0), `d0 \t# mem exp \t# watch out\n"
                                             else "movq \t(`s0), `d0 \t# watch out\n",
                                       src=[munchExp e], dst=[r], jump=NONE}))

        | munchExp(T.TEMP t) =
            t

        | munchExp(T.ESEQ(s, e)) =
            (munchStm s;
            munchExp e)

        | munchExp(T.NAME n) =
            result(fn r => emit(A.OPER{assem="movq \t$" ^ S.name n ^ ", `d0\n",
                                       src=nil, dst=[r], jump=NONE}))

        | munchExp(T.CONST i) =
            result(fn r => emit(A.OPER{assem="movq \t$" ^ Int.toString i ^ ", `d0\n",
                                       src=nil, dst=[r], jump=NONE}))

        | munchExp(T.CALL(T.NAME n, args)) =
            let
              val args' = munchArgs(0, args)
            in
              (result(fn r => emit(A.OPER{assem="call \t" ^ S.name n ^ "\n",
                                         src=args',
                                         dst=F.callerSaves, jump=NONE}));
              F.RV)
            end
        | munchExp(T.CALL(e, args)) =
            let
              val e' = munchExp e
              val args' = munchArgs(0, args)
            in
              result(fn r => emit(A.OPER{assem="call \t*`s0\n",
                                         src=e' :: args',
                                         dst=F.callerSaves, jump=NONE}));
              F.RV
            end

    in
      munchStm stm;
      rev(!ilist)
    end
end
