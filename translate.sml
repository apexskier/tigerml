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

  val unEx : exp -> Tree.exp
  val unNx : exp -> Tree.stm
  val unCx : exp -> (Temp.label * Temp.label -> Tree.stm)

  val assignExp : exp * exp -> exp
  val ifThenElseExp : exp * exp * exp -> exp
  val ifThenExp : exp * exp -> exp
  val intExp : int -> exp
  val seqExp : exp list -> exp
  val simpleVar : access * level -> exp
  val stringExp : string -> exp
  val letExp : exp list * exp -> exp

  val procEntryExit : level * exp -> unit
  val getResult : unit -> Frame.frag list
end

structure Translate : TRANSLATE =
struct
  structure Frame = Amd64Frame
  structure F = Frame
  structure T = Tree
  structure E = ErrorMsg

  datatype level = Outer
                 | Level of {frame:Frame.frame, parent:level} * unit ref
  type access = level * Frame.access
  datatype exp = Ex of Tree.exp                            (* expression with result *)
               | Nx of Tree.stm                            (* no result *)
               | Cx of Temp.label * Temp.label -> Tree.stm (* conditional *)

  val outermost = Outer
  val fragments = ref(nil:Frame.frag list)

  fun newLevel{parent, name, formals} =
    (* create a new frame, inserting an extra parameter for the static link *)
    Level({frame=Frame.newFrame({name=name, formals=true :: formals}), parent=parent}, ref ())

  fun formals(level) =
    case level
      of Outer => []
       | Level({frame, parent}, _) =>
        Frame.formals(frame)

  fun allocLocal(level) =
    case level
      of Outer =>
        raise Fail "Allocating locals at outermost level"
       | Level({frame, parent}, _) =>
        (fn(g) =>
          (level, Frame.allocLocal(frame)(g)))

  (* Utilities *)
  val emptyEx = Ex(T.CONST 42)

  fun error(msg) =
    (print (msg ^ "\n");
    raise E.Error)

  fun seq(nil) = unNx(emptyEx)
    | seq([s]) = s
    | seq(h::t) = T.SEQ(h, seq(t))

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

  and unNx(Ex e) = T.EXP(e)
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
          T.MEM(T.BINOP(T.PLUS, T.CONST 0, staticLink(defLevel, parent)))
    | staticLink(_, Outer) = T.TEMP F.FP

  (* Translation *)

  fun assignExp(var, exp) =
    Nx(T.MOVE(unEx var, unEx exp))

  fun ifThenElseExp(test, th, el) =
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
         | (_, _) =>
             error "illegal: incompatable then and else"
    end

  fun ifThenExp(test, th) =
    let
      val testCx = unCx test
      val thLab = Temp.newLabel()
      val finLab = Temp.newLabel()
      val r = Temp.newTemp()
    in
      case th
        of (Ex _) =>
          Ex(T.ESEQ(seq[(testCx)(thenLab, finLab),
                        T.LABEL thLab,
                        T.MOVE(T.TEMP r, unEx th),
                        T.LABEL finLab],
                    T.TMEP r))
         | (Nx _) =>


  fun intExp(i) =
    Ex(T.CONST i)

  fun seqExp(nil) =
        emptyEx
    | seqExp([exp]) =
        exp
    | seqExp(h::t) =
        Ex(T.ESEQ(unNx h, unEx(seqExp t)))

  fun simpleVar(access, level) =
    let
      val (acclev, fracc) = access
    in
      case acclev
        of Level({frame=frame, parent=parentLevel}, _) =>
          Ex(F.exp(fracc)(staticLink(#1 access, level)))
         | Outer =>
          error "illegal: variable access at outermost level"
    end

  fun stringExp(s) =
    let
      val l = Temp.newLabel()
    in
      fragments := Frame.STRING(l, s) :: !fragments;
      Ex(T.NAME l)
    end

  fun letExp(nil, body) =
        body
    | letExp(decs, body) =
        Ex(T.ESEQ(seq(List.map unNx decs), unEx body))

  fun procEntryExit(Level({frame, parent}, _), body:exp) =
        fragments := F.PROC{body=unNx(body)
                                 (* seq[T.MOVE(T.TEMP(hd F.argregs), T.TEMP F.FP),
                                     T.MOVE(T.TEMP Frame.RA unEx body)] *),
                            frame=frame} :: !fragments
    | procEntryExit(Outer, body:exp) =
        print "procEntryExit entering at outer level\n"

  fun getResult() = !fragments
end
