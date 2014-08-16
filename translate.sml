signature TRANSLATE =
sig
  type level
  type access (* not the same as FRAME.access *)
  type exp

  structure Frame : FRAME

  val outermost : level
  val fragments : Frame.frag list ref
  val emptyEx : exp

  val newLevel : {parent:level, name:Temp.label, formals:bool list} -> level
  val formals : level -> Frame.access list
  val allocLocal : level -> bool -> access
  val getAccesses : level -> access list

  val unEx : exp -> Tree.exp
  val unNx : exp -> Tree.stm
  val unCx : exp -> (Temp.label * Temp.label -> Tree.stm)

  val arithExp : {oper:Absyn.oper, left:exp, right:exp} -> exp
  val arrayExp : {size:exp, init:exp} -> exp
  val assignExp : exp * exp -> exp
  val breakExp : Temp.label -> exp
  val callExp : {name:Temp.label, level:level, funLevel:level, args:exp list} -> exp
  val compareIntExp : {oper:Absyn.oper, left:exp, right:exp} -> exp
  val compareNil : unit -> exp
  val compareStrExp : {oper:Absyn.oper, left:exp, right:exp} -> exp
  val compareRefEqExp : exp * exp -> exp
  val fieldVar : {var:exp, pos:int} -> exp
  val forExp : {var:exp, body:exp, lo:exp, hi:exp, fin:Temp.label} -> exp
  val ifThenElseExp : exp * exp * exp -> exp
  val ifThenExp : exp * exp -> exp
  val intExp : int -> exp
  val letExp : exp list * exp -> exp
  val newExp : {attrs:exp list, level:level} -> exp
  val newMethod : {name:Temp.label, level:level, funLevel:level} -> exp
  val recordExp : exp list -> exp
  val seqExp : exp list -> exp
  val simpleVar : access * level -> exp
  val stringExp : string -> exp
  val subscriptVar : {var:exp, loc:exp} -> exp
  val varDec : {init:exp, level:level, access:access} -> exp
  val whileExp : {test:exp, body:exp, fin:Temp.label} -> exp

  val procEntryExit : level * exp * bool -> unit
  val getResult : unit -> Frame.frag list
end

structure Translate : TRANSLATE =
struct
  structure A = Absyn
  structure Frame = Amd64Frame
  structure F = Frame
  structure T = Tree
  structure E = ErrorMsg
  val error = ErrorMsg.impossible

  datatype level = Outer
                 | Level of {frame:F.frame, parent:level} * unit ref
  type access = level * F.access
  datatype exp = Ex of Tree.exp                            (* expression with result *)
               | Nx of Tree.stm                            (* no result *)
               | Cx of Temp.label * Temp.label -> Tree.stm (* conditional *)

  val outermost = Outer
  val fragments = ref(nil:F.frag list)

  val noBreak = Temp.newLabel()
  val breakLabel = ref noBreak

  fun newLevel{parent, name, formals} =
    (* create a new frame, inserting an extra parameter for the static link *)
    Level({frame=F.newFrame({name=name, formals=true :: formals}), parent=parent}, ref ())

  fun formals level =
    case level
      of Outer => []
       | Level({frame, parent}, _) =>
        F.formals frame

  fun allocLocal level =
    case level
      of Outer =>
        raise Fail "Allocating locals at outermost level"
       | Level({frame, parent}, _) =>
        (fn g =>
          (level, F.allocLocal(frame)(g)))

  fun getAccesses level =
    case level
      of Outer =>
        raise Fail "Allocating locals at outermost level"
       | Level({frame=frame as {name, formals, accesses, locals, entree}, parent}, _) => map (fn a => (level, a)) (tl accesses)

  (* Utilities *)
  val emptyEx = Ex(T.CONST 0)

  (* fun runtimeErr msg =
    let
      val errLab = Temp.newLabel()
      val errTree =
        seq[T.LABEL errLab,
            T.EXP(T.CALL(T.NAME(Temp.namedLabel("print"),
                         [unEx stringExp("rutime error: " ^ msg)])))]
    in
      (errLab, errTree)
    end *)

  fun seq nil = unNx emptyEx
    | seq([s]) = s
    | seq(h::t) = T.SEQ(h, seq t)

  and unEx(Ex e) = e
    | unEx(Cx stm) =
        let
          val r = Temp.newTemp()
          val t = Temp.newLabel()
          and f = Temp.newLabel()
        in
          T.ESEQ(seq[T.MOVE(T.TEMP r, T.CONST 1),
                     stm(t, f),
                     T.LABEL f,
                     T.MOVE(T.TEMP r, T.CONST 0),
                     T.LABEL t],
                 T.TEMP r)
        end
    | unEx(Nx s) =
        T.ESEQ(s, T.CONST 0)

  and unCx(Ex(T.CONST 0)) =
        (fn(t, f) => T.JUMP(T.NAME f, [f]))
    | unCx(Ex(T.CONST _)) =
        (fn(t, f) => T.JUMP(T.NAME t, [t]))
    | unCx(Ex e) =
        (fn(t, f) => T.CJUMP(T.NE, e, T.CONST 0, t, f))
    | unCx(Cx stm) = stm
    | unCx(Nx _) =
        error "illegal: using statement as conditional"

  and unNx(Ex e) = T.EXP e
    | unNx(Cx stm) =
        let
          val r = Temp.newTemp()
          val t = Temp.newLabel()
          and f = Temp.newLabel()
        in
          stm(t, f)
        end
    | unNx(Nx s) = s

  fun levEq(Level(_, a), Level(_, b)) =
        a = b
    | levEq(Outer, Outer) = true
    | levEq(_, _) = false

  fun staticLink(defLevel, curLevel as Level({frame:F.frame, parent:level}, _)) =
        if levEq(defLevel, curLevel) then
          T.TEMP F.FP
        else
          T.MEM(staticLink(defLevel, parent))
    | staticLink(_, Outer) = T.TEMP F.FP

  (* Translation *)

  fun arithExp{oper, left, right} =
    let
      val oper' =
        case oper
          of A.PlusOp => T.PLUS
           | A.MinusOp => T.MINUS
           | A.TimesOp => T.MUL
           | A.DivideOp => T.DIV
           | _ =>
               ErrorMsg.impossible "non-arithmetic operator"
    in
      Ex(T.BINOP(oper', unEx left, unEx right))
    end

  and arrayExp{size, init} =
    Ex(F.externalCall("initArray", [unEx size, unEx init]))

  and assignExp(var, exp) =
    Nx(T.MOVE(unEx var, unEx exp))

  and breakExp lab =
    Nx(T.JUMP(T.NAME lab, [lab]))

  and callExp{name, level, funLevel, args} =
    let
      val predefs = ["print", "printint", "flush", "getchar", "ord", "chr", "size", "substring", "concat", "not", "exit"]
      val nameStr = Symbol.name name
      fun eq a = a = nameStr
    in
      if List.exists eq predefs then
        Ex(T.CALL(T.NAME name, List.map unEx args))
      else
        Ex(T.CALL(T.NAME name, staticLink(level, funLevel) :: List.map unEx args))
    end

  and compareIntExp{oper, left, right} =
    let
      val oper' =
        case oper
          of A.EqOp => T.EQ
           | A.NeqOp => T.NE
           | A.LtOp => T.LT
           | A.LeOp => T.LE
           | A.GtOp => T.GT
           | A.GeOp => T.GE
           | _ =>
               ErrorMsg.impossible "non-comparison operator"
      val cx =
        fn(t, f) =>
          T.CJUMP(oper', unEx left, unEx right, t, f)
    in
      Cx cx (* TODO: should this produce one or zero? *)
    end

  and compareNil() =
    Ex(T.CONST 0) (* always false *)

  and compareStrExp{oper, left, right} =
    let
      val oper' =
        case oper
          of A.EqOp => "stringEqual"
           | A.NeqOp => "strNeq"
           | A.LtOp => "strLt"
           | A.LeOp => "strLe"
           | A.GtOp => "strGt"
           | A.GeOp => "strGe"
           | _ =>
               ErrorMsg.impossible "non-comparison operator when comparing strings"
    in
      Ex(F.externalCall(oper', [unEx left, unEx right]))
    end

  and compareRefEqExp(left, right) =
    Cx(fn(t, f) => T.CJUMP(T.EQ, unEx left, unEx right, t, f))

  and fieldVar{var, pos} =
    if pos = 0 then
      Ex(T.MEM(unEx var))
    else
      Ex(T.MEM(T.BINOP(T.PLUS, unEx var, T.CONST(pos * F.wordsize))))

  and forExp{var, body, lo, hi, fin} =
    let
      val bodyLab = Temp.newLabel()
      and finLab = fin
      val _ = breakLabel := finLab
      val testCx =
        fn(t, f) =>
          T.CJUMP(T.GE, unEx var, unEx hi, t, f)
      val testCx' =
        fn(t, f) =>
          T.CJUMP(T.LE, unEx var, unEx hi, t, f)
    in
      Nx(seq[T.MOVE(unEx var, unEx lo),
             (testCx)(finLab, bodyLab),
             T.LABEL bodyLab,
             unNx body,
             unNx(assignExp(var, arithExp{oper=A.PlusOp, left=var, right=Ex(T.CONST 1)})),
             (testCx')(finLab, bodyLab),
             T.LABEL finLab])
    end

  and ifThenElseExp(test, th, el) =
    let
      val testCx = unCx test
      val thLab = Temp.newLabel()
      and elLab = Temp.newLabel()
      and finLab = Temp.newLabel()
      val r = Temp.newTemp()
    in
      case (th, el)
        of (Ex _, Ex _) =>
          Ex(T.ESEQ(seq[(testCx)(thLab, elLab),
                        T.LABEL thLab,
                        T.MOVE(T.TEMP r, unEx th),
                        T.JUMP(T.NAME finLab, [finLab]),
                        T.LABEL elLab,
                        T.MOVE(T.TEMP r, unEx el),
                        T.LABEL finLab], T.TEMP r))
         | (Nx _, Nx _) =>
          Nx(seq[(testCx)(thLab, elLab),
                 T.LABEL thLab,
                 unNx th,
                 T.JUMP(T.NAME finLab, [finLab]),
                 T.LABEL elLab,
                 unNx el,
                 T.LABEL finLab])
         | (Cx _, Cx _) =>
          Cx(fn(t, f) =>
              seq[(testCx)(thLab, elLab),
                  T.LABEL thLab,
                  (unCx th)(t, f),
                  T.JUMP(T.NAME finLab, [finLab]),
                  T.LABEL elLab,
                  (unCx el)(t, f),
                  T.LABEL finLab])
         | (a, b) =>
          Ex(T.ESEQ(seq[(testCx)(thLab, elLab),
                        T.LABEL thLab,
                        T.MOVE(T.TEMP r, unEx th),
                        T.JUMP(T.NAME finLab, [finLab]),
                        T.LABEL elLab,
                        T.MOVE(T.TEMP r, unEx el),
                        T.LABEL finLab], T.TEMP r))
    end

  and ifThenExp(test, th) =
    let
      val testCx = unCx test
      val thLab = Temp.newLabel()
      val finLab = Temp.newLabel()
      val r = Temp.newTemp()
    in
      case th
        of (Ex _) =>
          Ex(T.ESEQ(seq[(testCx)(thLab, finLab),
                        T.LABEL thLab,
                        T.MOVE(T.TEMP r, unEx th),
                        T.LABEL finLab],
                    T.TEMP r))
         | (Nx _) =>
          Nx(seq[(testCx)(thLab, finLab),
                 T.LABEL thLab,
                 T.MOVE(T.TEMP r, unEx th),
                 T.LABEL finLab])
         | (Cx _) =>
          Cx(fn(t, f) =>
            seq[(testCx)(thLab, finLab),
                T.LABEL thLab,
                (unCx th)(t, f),
                T.LABEL finLab])
    end

  and intExp i =
    Ex(T.CONST i)

  and letExp(nil, body) =
        body
    | letExp(decs, body) =
        Ex(T.ESEQ(seq(List.map unNx decs), unEx body))

  and newExp{attrs, level} =
    recordExp attrs

  and newMethod{name, level, funLevel} =
    Ex(T.NAME name) (* TODO *)

  and recordExp fields =
    let
      val l = Temp.newTemp()
      val i = ref 0
      fun insertField field =
        let
          val pos = !i
        in
          i := !i + 1;
          T.MOVE(T.MEM(if pos = 0 then
            T.TEMP l
          else
            T.BINOP(T.PLUS, T.TEMP l, T.CONST(pos * F.wordsize))), unEx field)
        end
      val size = length fields
      val (fieldsTree) = seq(map insertField fields)
    in
      Ex(T.ESEQ(T.SEQ(T.MOVE(T.TEMP l,
                             F.externalCall("allocRecord", [T.CONST size])),
                      fieldsTree),
                T.TEMP l))
    end

  and seqExp nil =
        emptyEx
    | seqExp([exp]) =
        exp
    | seqExp(h::t) =
        Ex(T.ESEQ(unNx h, unEx(seqExp t)))

  and simpleVar(access, level) =
    let
      val (acclev, fracc) = access
    in
      case acclev
        of Level({frame=frame, parent=parentLevel}, _) =>
          Ex(F.exp(fracc)(staticLink(acclev, level)))
         | Outer =>
          error "illegal: variable access at outermost level"
    end

  and stringExp s =
    let
      fun eq frag =
        case frag
          of F.STRING(l, s') => s' = s
           | _ => false
      val mtch = List.find eq (!fragments)
    in
      case mtch
        of SOME(F.STRING(l, _)) => Ex(T.NAME l)
         | _ =>
          let
            val l = Temp.newLabel()
          in
            fragments := F.STRING(l, s) :: !fragments;
            Ex(T.NAME l)
          end
    end

  and subscriptVar{var, loc} =
    let
      (* TODO: bounds checking *)
      val errLab = Temp.newLabel()
      val hiChkLab = Temp.newLabel()
      and goodLab = Temp.newLabel()
      val loc' = unEx loc
      val var' = unEx var
      val loChk =
        fn(t, f) =>
          T.CJUMP(T.GT, T.CONST 0, loc', t, f)
      val hiChk =
        fn(t, f) =>
          T.CJUMP(T.LT, var', loc', t, f)
    in
      (* Ex(T.ESEQ(seq[(loChk)(errLab, hiChkLab),
                    T.LABEL hiChkLab,
                    (hiChk)(errLab, goodLab),
                    T.LABEL errLab,
                    T.EXP(T.CALL(T.NAME(Temp.namedLabel("print")),
                                 [unEx(stringExp("runtime error: " ^ "subscripting out of bounds" ^ "\n"))])),
                    T.LABEL goodLab], *)
                Ex(T.MEM(T.BINOP(T.PLUS, var', T.BINOP(T.MUL, loc', T.CONST F.wordsize))))(*))*)
    end

  and varDec{init, level, access} =
    let
      val place = simpleVar(access, level)
    in
      Nx(T.MOVE(unEx place, unEx init))
    end

  and whileExp{test, body, fin} =
    let
      val testCx = unCx test
      val idx = Temp.newTemp()
      val finLab = fin
      and testLab = Temp.newLabel()
      and bodyLab = Temp.newLabel()
      val _ = breakLabel := finLab
    in
      Nx(seq[T.LABEL testLab,
             (testCx)(bodyLab, finLab),
             T.LABEL bodyLab,
             unNx body,
             T.JUMP(T.NAME testLab, [testLab]),
             T.LABEL finLab])
    end



  fun procEntryExit(Level({frame, parent}, _), body:exp, returns:bool) =
        let
          val tree =
            if returns then
              T.MOVE(T.TEMP F.RV, unEx body)
            else
              T.SEQ(unNx body, T.MOVE(T.TEMP F.RV, T.CONST 0))
        in
          fragments := F.PROC{body=tree,
                              frame=frame} :: !fragments
        end
    | procEntryExit(Outer, body:exp, returns:bool) =
        print "procEntryExit entering at outer level\n"

  fun getResult() = !fragments
end
