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
            (emit(A.OPER{assem="cmp \t`s0, $" ^ Int.toString i ^ "\n", (* TODO: this appears to be an illegal statement *)
                        src=[munchExp e],
                        dst=nil,
                        jump=NONE});
            emit(A.OPER{assem=assemOperJmp oper ^ " " ^
                              (if oper = T.NE then S.name l2 else S.name l1) ^ "\n",
                        src=nil, dst=nil, jump=SOME[l1, l2]}))
        | munchStm(T.CJUMP(oper, e, T.CONST i, l1, l2)) =
            (emit(A.OPER{assem="cmp \t$" ^ Int.toString i ^ ", `s0\n",
                        src=[munchExp e],
                        dst=nil,
                        jump=NONE});
            emit(A.OPER{assem=assemOperJmp oper ^ " " ^
                              (if oper = T.NE then S.name l2 else S.name l1) ^ "\n",
                        src=nil, dst=nil, jump=SOME[l1, l2]}))
        | munchStm(T.CJUMP(oper, e1, e2, l1, l2)) =
            (emit(A.OPER{assem="cmp \t`s1, `s0\n",
                        src=[munchExp e1, munchExp e2],
                        dst=nil,
                        jump=NONE});
            emit(A.OPER{assem=assemOperJmp oper ^ " " ^
                              (if oper = T.NE then S.name l2 else S.name l1) ^ "\n",
                        src=nil, dst=nil, jump=SOME[l1, l2]}))

        | munchStm(T.MOVE(T.TEMP t0, T.TEMP t1)) =
            if t0 <> t1 then
              emit(A.MOVE{assem="movq \t`s0, `d0 \t# skipped a step\n",
                          src=t1,
                          dst=t0})
            else () (* NOTE: skipping move as args are the same *)
        | munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS, T.CONST i, T.TEMP t)), T.CONST j)) =
            emit(A.OPER{assem="movq \t$" ^ Int.toString j ^ ", " ^ intStr i ^ "(`d0)\n",
                        src=nil,
                        dst=[t],
                        jump=NONE})
        | munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS, T.TEMP t, T.CONST i)), T.CONST j)) =
            emit(A.OPER{assem="movq \t$" ^ Int.toString j ^ ", " ^ intStr i ^ "(`d0)\n",
                        src=nil,
                        dst=[t],
                        jump=NONE})
        | munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS, T.CONST i, e)), T.CONST j)) =
            emit(A.OPER{assem="movq \t$" ^ Int.toString j ^ ", " ^ intStr i ^ "(`d0)\n",
                        src=nil,
                        dst=[munchExp e],
                        jump=NONE})
        | munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS, e, T.CONST i)), T.CONST j)) =
            emit(A.OPER{assem="movq \t$" ^ Int.toString j ^ ", " ^ intStr i ^ "(`d0)\n",
                        src=nil,
                        dst=[munchExp e],
                        jump=NONE})
        | munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS, T.CONST i, T.TEMP t)), T.NAME n)) =
            emit(A.OPER{assem="movq \t$" ^ S.name n ^ ", " ^ intStr i ^ "(`d0)\n",
                        src=nil,
                        dst=[t],
                        jump=NONE})
        | munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS, T.TEMP t, T.CONST i)), T.NAME n)) =
            emit(A.OPER{assem="movq \t$" ^ S.name n ^ ", " ^ intStr i ^ "(`d0)\n",
                        src=nil,
                        dst=[t],
                        jump=NONE})
        | munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS, T.CONST i, e)), T.NAME n)) =
            emit(A.OPER{assem="movq \t$" ^ S.name n ^ ", " ^ intStr i ^ "(`d0)\n",
                        src=nil,
                        dst=[munchExp e],
                        jump=NONE})
        | munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS, e, T.CONST i)), T.NAME n)) =
            emit(A.OPER{assem="movq \t$" ^ S.name n ^ ", " ^ intStr i ^ "(`d0)\n",
                        src=nil,
                        dst=[munchExp e],
                        jump=NONE})
        | munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS, T.CONST i, T.TEMP t)), T.TEMP n)) =
            emit(A.OPER{assem="movq \t`s0, " ^ intStr i ^ "(`d0)\n",
                        src=[n],
                        dst=[t],
                        jump=NONE})
        | munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS, T.TEMP t, T.CONST i)), T.TEMP n)) =
            emit(A.OPER{assem="movq \t`s0, " ^ intStr i ^ "(`d0)\n",
                        src=[n],
                        dst=[t],
                        jump=NONE})
        | munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS, T.CONST i, e)), T.TEMP n)) =
            emit(A.OPER{assem="movq \t`s0, " ^ intStr i ^ "(`d0)\n",
                        src=[n],
                        dst=[munchExp e],
                        jump=NONE})
        | munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS, e, T.CONST i)), T.TEMP n)) =
            emit(A.OPER{assem="movq \t`s0, " ^ intStr i ^ "(`d0)\n",
                        src=[n],
                        dst=[munchExp e],
                        jump=NONE})
        | munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS, T.TEMP t, T.CONST i)), e)) =
            emit(A.OPER{assem="movq \t`s0, " ^ intStr i ^ "(`d0)\n",
                        src=[munchExp e],
                        dst=[t],
                        jump=NONE})
        | munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS, T.CONST i, T.TEMP t)), e)) =
            emit(A.OPER{assem="movq \t`s0, " ^ intStr i ^ "(`d0)\n",
                        src=[munchExp e],
                        dst=[t],
                        jump=NONE})
        | munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS, e1, T.CONST i)), e2)) =
            emit(A.OPER{assem="movq \t`s0, " ^ intStr i ^ "(`d0)\n",
                        src=[munchExp e2],
                        dst=[munchExp e1],
                        jump=NONE})
        | munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS, T.CONST i, e1)), e2)) =
            emit(A.OPER{assem="movq \t`s0, " ^ intStr i ^ "(`d0)\n",
                        src=[munchExp e2],
                        dst=[munchExp e1],
                        jump=NONE})
        | munchStm(T.MOVE(T.CONST j, T.MEM(T.BINOP(T.PLUS, T.CONST i, T.TEMP t)))) =
            ErrorMsg.impossible "moving memory into constant"
        | munchStm(T.MOVE(T.CONST j, T.MEM(T.BINOP(T.PLUS, T.TEMP t, T.CONST i)))) =
            ErrorMsg.impossible "moving memory into constant"
        | munchStm(T.MOVE(T.NAME n, T.MEM(T.BINOP(T.PLUS, T.CONST i, T.TEMP t)))) =
            ErrorMsg.impossible "moving memory into name"
        | munchStm(T.MOVE(T.NAME n, T.MEM(T.BINOP(T.PLUS, T.TEMP t, T.CONST i)))) =
            ErrorMsg.impossible "moving memory into name"
        | munchStm(T.MOVE(T.TEMP n, T.MEM(T.BINOP(T.PLUS, T.CONST i, T.TEMP t)))) =
            emit(A.OPER{assem="movq \t" ^ intStr i ^ "(`d0), `s0\n",
                        src=[t],
                        dst=[n],
                        jump=NONE})
        | munchStm(T.MOVE(T.TEMP n, T.MEM(T.BINOP(T.PLUS, T.TEMP t, T.CONST i)))) =
            emit(A.OPER{assem="movq \t" ^ intStr i ^ "(`d0), `s0\n",
                        src=[t],
                        dst=[n],
                        jump=NONE})
        | munchStm(T.MOVE(e, T.MEM(T.BINOP(T.PLUS, T.TEMP t, T.CONST i)))) =
            emit(A.OPER{assem="movq \t" ^ intStr i ^ "(`d0), `s0\n",
                        src=[t],
                        dst=[munchExp e],
                        jump=NONE})
        | munchStm(T.MOVE(e, T.MEM(T.BINOP(T.PLUS, T.CONST i, T.TEMP t)))) =
            emit(A.OPER{assem="movq \t" ^ intStr i ^ "(`d0), `s0\n",
                        src=[t],
                        dst=[munchExp e],
                        jump=NONE})
        | munchStm(T.MOVE(T.MEM(T.TEMP t0), T.TEMP t1)) =
            emit(A.OPER{assem="movq \t`s0, (`d0)\n",
                        src=[t1, t0], dst=[t0], jump=NONE})
        | munchStm(T.MOVE(T.TEMP t0, T.MEM(T.TEMP t1))) =
            emit(A.OPER{assem="movq \t(`s0), `d0\n",
                        src=[t1], dst=[t0], jump=NONE})
        | munchStm(T.MOVE(T.TEMP t0, T.BINOP(oper, T.CONST i, T.TEMP t1))) =
            (case oper
              of T.DIV =>
                ErrorMsg.impossible "not implemented" (* munchDiv() *)
               | _ =>
                if t1 = t0 then
                  emit(A.OPER{assem=assemOper oper ^ " \t$" ^ Int.toString i ^ ", `s0 \t# coalescing a temp to const + temp instruction\n",
                              src=[t0, t1], dst=[t0], jump=NONE})
                else
                  (emit(A.MOVE{assem="movq \t`s0, `d0\n",
                              src=t1, dst=t0});
                  emit(A.OPER{assem=assemOper oper ^ " \t$" ^ Int.toString i ^ ", `d0\n",
                              src=[t0], dst=[t0], jump=NONE})))
        | munchStm(T.MOVE(T.TEMP t0, T.BINOP(oper, T.TEMP t1, T.CONST i))) =
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
                  emit(A.OPER{assem=assemOper oper ^ " \t$" ^ Int.toString i ^ ", `d0 \t# test\n",
                              src=[t0], dst=[t0], jump=NONE})))
        | munchStm(T.MOVE(T.TEMP t0, T.BINOP(oper, T.TEMP t1, T.TEMP t2))) =
            (case oper
              of T.DIV =>
                ErrorMsg.impossible "not implemented" (* munchDiv() *)
               | _ =>
                if t0 = t1 then
                  emit(A.OPER{assem=assemOper oper ^ " \t`s1, `d0 \t# coalescing a temp to temp + temp instruction\n",
                              src=[t2, t1], dst=[t0], jump=NONE})
                else
                  if t0 = t2 then
                    emit(A.OPER{assem=assemOper oper ^ " \t`s1, `d0 \t# coalescing a temp to temp + temp instruction\n",
                                src=[t1, t2], dst=[t0], jump=NONE})
                  else
                    (emit(A.MOVE{assem="movq \t`s0, `d0 \t# src: "^Temp.makeString t2^" dst: "^Temp.makeString t0^"\n",
                                src=t2, dst=t0});
                    emit(A.OPER{assem=assemOper oper ^ " \t`s0, `d0 \t# didn't coalesce src: "^Temp.makeString t1^" dst: "^Temp.makeString t0^"\n",
                                src=[t1, t0], dst=[t0], jump=NONE})))
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
            emit(A.MOVE{assem="movq \t`s0, `d0\n",
                        src=munchExp e2,
                        dst=munchExp e1})

        | munchStm(T.EXP e) =
            (munchExp e; ())

      and munchArgs(argnum, arg::args) = (* TODO: handle more parameters than arg registers *)
            let
              val arg' = List.nth(F.argRegs, argnum)
            in
              emit(A.MOVE{assem="movq \t`s0, `d0 \t# arg " ^ Int.toString argnum ^ "\n",
                          src=munchExp arg, dst=arg'});
              arg' :: munchArgs(argnum + 1, args)
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
            result(fn r => emit(A.OPER{assem="movq \t" ^ intStr i ^ "(`s0), `d0\n",
                                       src=[munchExp e], dst=[r], jump=NONE}))
        | munchExp(T.MEM(T.BINOP(T.PLUS, T.CONST i, e))) =
            result(fn r => emit(A.OPER{assem="movq \t" ^ intStr i ^ "(`s0), `d0\n",
                                       src=[munchExp e], dst=[r], jump=NONE}))
        | munchExp(T.MEM(e)) =
            result(fn r => emit(A.OPER{assem="movq \t(`s0), `d0\n",
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
