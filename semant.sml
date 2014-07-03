signature SEMANT =
sig
  val transProg : Absyn.exp -> unit

  type venv = Env.enventry Symbol.table
  type tenv = Types.ty Symbol.table
  type expty = {exp: unit, ty: Types.ty}

  val transVar : venv * tenv * Absyn.var -> expty
  val transExp : venv * tenv * Absyn.exp -> expty
  val transDec : venv * tenv * Absyn.dec -> {venv: venv, tenv: tenv}
  val transDecs : venv * tenv * Absyn.dec list -> {venv: venv, tenv: tenv}
  val transTy : tenv * Absyn.ty -> Types.ty
end

structure Semant : SEMANT =
struct

  structure A = Absyn
  structure E = Env
  structure T = Types
  structure S = Symbol

  val error = ErrorMsg.error
  val errExpty = {exp=(), ty=T.UNIT}

  type venv = E.enventry S.table
  type tenv = T.ty S.table
  type expty = {exp: unit, ty: T.ty}

  (* Utility functions *)
  fun actTy(T.NAME(name, ty)) =
    (case !ty
      of NONE => (error 0 ("unknown name " ^ S.name name); T.UNIT)
       | SOME t => actTy t)
    | actTy t = t

  fun getSym(s: S.symbol, _) = s

  fun tyEq(a, b) =
    let val A = actTy a
        val B = actTy b
    in
      (*
      case A
        of T.RECORD _ => print "-----> record ?= "
         | T.NIL => print "-----> nil ?= "
         | T.INT => print "-----> int ?= "
         | T.STRING => print "-----> string ?= "
         | T.ARRAY _ => print "-----> array ?= "
         | T.NAME _ => print "-----> name ?= "
         | T.UNIT => print "-----> unit ?= "
         | T.CLASS _ => print "-----> class ?= "
         ;
      case B
        of T.RECORD _ => print "record\n"
         | T.NIL => print "nil\n"
         | T.INT => print "int\n"
         | T.STRING => print "string\n"
         | T.ARRAY _ => print "array\n"
         | T.NAME _ => print "name\n"
         | T.UNIT => print "unit\n"
         | T.CLASS _ => print "class\n"
         ; *)
      if A = B then true
      else
        case A
          of T.NIL =>
            ( case B
                of T.RECORD(_, _) => true
                 | _ => false )
           | T.RECORD(c, d) =>
            ( case B
                of T.RECORD(c, d) => true
                 | T.NIL => true
                 | _ => false )
           | _ => false
    end

  fun checkTy(req, ty, pos) =
    let
      val strTy =
        case req
          of T.RECORD _ => "record"
           | T.NIL => "nil"
           | T.INT => "int"
           | T.STRING => "string"
           | T.ARRAY _ => "array"
           | T.NAME _ => "name"
           | T.UNIT => "unit"
           | T.CLASS _ => "class"
    in
      if ty <> req then
        (error pos ("wrong type: expected " ^ strTy);
        req)
      else ty
    end

  (* Main visible functions *)
  fun transVar(venv, tenv, var) =
    let
      fun trvar(A.SimpleVar(id, pos)) =
            (case S.look(venv, id)
              of SOME(E.VarEntry{ty}) => {exp=(), ty=actTy ty}
               | SOME(E.FunEntry{formals, result}) =>
                 (error pos ("function name used as var: '" ^ S.name id ^ "'");
                 errExpty)
               | NONE =>
                 (error pos ("unknown variable '" ^ S.name id ^ "'");
                 errExpty))
        | trvar(A.FieldVar(var, id, pos)) =
            (case #ty(trvar var)
              of T.RECORD(fields, _) =>
                  (* look up field *)
                  let fun matchField(field) =
                            id = getSym field
                  in
                    case List.find matchField fields
                      of SOME(_, ty) => {exp=(), ty=ty}
                       | NONE => (
                          error pos ("record field '" ^ S.name id ^ "' not found");
                          errExpty)
                  end
               | _ => (
                  error pos ("accessing field '" ^ S.name id ^ "' on non-record");
                  errExpty))
        | trvar(A.SubscriptVar(var, exp, pos)) =
            (case #ty(trvar var)
              of T.ARRAY(ty, _) => {exp=(), ty=ty}
               | _ => (error pos "subscripting non-array";
                  errExpty))
    in
      trvar var
    end

  and transExp(venv, tenv, exp) =
    let
      fun trexp(A.VarExp var) =
            {exp=(), ty=(#ty(transVar(venv, tenv, var)))}
        | trexp(A.NilExp) =
            {exp=(), ty=T.NIL}
        | trexp(A.IntExp i) =
            {exp=(), ty=T.INT}
        | trexp(A.StringExp s) =
            {exp=(), ty=T.STRING}
        | trexp(A.CallExp{func, args, pos}) =
            (case S.look(venv, func)
              of SOME(E.FunEntry{formals, result=resultTy}) =>
                  let
                    val frmsLen = length formals
                    val argsLen = length args
                    fun matchTy(a, f) =
                      let
                        val {exp=_, ty=ty} = trexp a
                      in
                        if tyEq(ty, f) then ()
                        else
                          error pos ("wrong argument type: '" ^ S.name func ^ "'")
                      end
                  in
                    if frmsLen <> argsLen then
                      (error pos ("incorrect number of arguments: found " ^ Int.toString argsLen ^ ", expected " ^ Int.toString frmsLen);
                      errExpty)
                    else
                      (ListPair.app matchTy(args, formals);
                      {exp=(), ty=resultTy})
                  end
               | SOME(E.VarEntry _) =>
                  (error pos ("attempting to call a regular variable: '" ^ S.name func ^ "'");
                  errExpty)
               | NONE =>
                  (error pos ("unknown function: '" ^ S.name func ^ "'");
                  errExpty))
        | trexp(A.OpExp{left, oper, right, pos}) =
            let
              val {exp=_, ty=lTy} = trexp left
              val {exp=_, ty=rTy} = trexp right
              fun arithmetic() =
                let
                  val _ = checkTy(T.INT, lTy, pos)
                in {exp=(), ty=checkTy(T.INT, rTy, pos)} end
              fun comparison() =
                case lTy
                  of T.INT =>
                    {exp=(), ty=T.INT}
                   | T.STRING =>
                    {exp=(), ty=T.INT}
                   | _ =>
                    (error pos "comparison operands must be integers or strings";
                    errExpty)
              fun comparisoneq() =
                case lTy
                  of T.INT =>
                    {exp=(), ty=T.INT}
                   | T.STRING =>
                    {exp=(), ty=T.INT}
                   | T.RECORD(_, un) => (* TODO *)
                    {exp=(), ty=T.INT}
                   | T.ARRAY(_, un) => (* TODO *)
                    {exp=(), ty=T.INT}
                   | T.NIL => (* TODO *)
                    {exp=(), ty=T.INT}
                   | T.CLASS(_, un) => (* TODO *)
                    {exp=(), ty=T.INT}
                   | _ =>
                    (error pos "equality operands cannot be UNIT or NAME";
                    errExpty)
            in
              if tyEq(lTy, rTy) then
                case oper
                  of A.PlusOp =>
                       arithmetic()
                   | A.MinusOp =>
                       arithmetic()
                   | A.TimesOp =>
                       arithmetic()
                   | A.DivideOp =>
                       arithmetic()
                   | A.EqOp =>
                       comparisoneq()
                   | A.NeqOp =>
                       comparisoneq()
                   | A.LtOp =>
                       comparison()
                   | A.LeOp =>
                       comparison()
                   | A.GtOp =>
                       comparison()
                   | A.GeOp =>
                       comparison()
              else
                (error pos "operands must have same type";
                errExpty)
            end
        | trexp(A.RecordExp{fields, typ, pos}) =
          errExpty (* TODO *)
        | trexp(A.SeqExp exps) =
            (case exps
              of nil => errExpty
               | _ =>
                let
                  val (lastexp, _) = List.last exps
                  val exps = List.take(exps, (length exps - 1)) (* drop last exp *)
                  val {exp=lastexp', ty=lastty} = trexp lastexp
                  fun getexps((exp, _), exps') =
                    let val {exp=newExp, ty} = trexp exp
                    in
                      newExp :: exps'
                    end
                  val _ = foldr getexps [] exps @ [lastexp']
                in
                  {exp=(), ty=lastty}
                end)
        | trexp(A.AssignExp{var, exp, pos}) =
            let
              val {exp=_, ty=varTy} = transVar(venv, tenv, var)
              val {exp=_, ty=expTy} = trexp exp
            in
              (if tyEq(varTy, expTy) then ()
              else
                error pos "assignment type mismatch";
              {exp=(), ty=varTy})
            end
        | trexp(A.IfExp{test, then'=th, else'=el, pos}) =
            let
              val {exp=_, ty=testTy} = trexp test
              val _ = checkTy(T.INT, testTy, pos)
              val {exp=_, ty=thenTy} = trexp th
            in
              case el
                of SOME(elseExp) =>
                  let
                    val {exp=_, ty=elseTy} = trexp elseExp
                  in
                    if tyEq(thenTy, elseTy) then
                      {exp=(), ty=thenTy}
                    else
                      (error pos "else type doesn't match then in if statement";
                      errExpty)
                  end
                 | NONE =>
                     {exp=(), ty=checkTy(T.UNIT, thenTy, pos)}
            end
        | trexp(A.WhileExp{test, body, pos}) =
            let
              val {exp=testExp, ty=tTy} = trexp test
              val {exp=bodyExp, ty=bTy} = trexp body
            in
              (checkTy(T.INT, tTy, pos);
              {exp=(), ty=checkTy(T.UNIT, bTy, pos)})
            end
        | trexp(A.ForExp{var, escape, lo, hi, body, pos}) =
          errExpty (* TODO *)
        | trexp(A.BreakExp pos) =
          errExpty (* TODO *)
        | trexp(A.LetExp{decs, body, pos}) =
            let
              val {venv=venv', tenv=tenv'} = transDecs(venv, tenv, decs)
              val {exp=bodyexp, ty=ty} = transExp(venv', tenv', body)
            in
              {exp=(), ty=ty}
            end
        | trexp(A.ArrayExp{typ, size, init, pos}) =
          errExpty (* TODO *)
        | trexp(A.MethodExp{var, name, args, pos}) =
          errExpty (* TODO *)
        | trexp(A.NewExp(name, pos)) =
          errExpty (* TODO *)
    in
      trexp exp
    end

  and transDecs(venv, tenv, decs) =
    let
      fun trdecs(dec, {venv, tenv}) =
        transDec(venv, tenv, dec)
    in
      foldl trdecs {venv=venv, tenv=tenv} decs
    end

  and transDec(venv, tenv, dec) =
    let
      fun trdec(A.FunctionDec fundecs) =
          {venv=venv, tenv=tenv} (* TODO *)
        | trdec(A.VarDec{name, escape, typ, init, pos}) =
            let
              val {exp=initExp, ty=initTy} = transExp(venv, tenv, init)
            in
              case typ
                of SOME(tyName, tyPos) =>
                  (case S.look(tenv, tyName)
                    of SOME(ty) =>
                      (if tyEq(initTy, ty) then ()
                      else error pos ("variable type '" ^ S.name tyName ^ "' doesn't match initialization");
                      {venv=S.enter(venv, name, E.VarEntry{ty=ty}), tenv=tenv})
                     | NONE =>
                      (error pos ("unknown type '" ^ S.name tyName ^ "' in variable declaration");
                      {venv=venv, tenv=tenv}))
                 | NONE =>
                  {venv=S.enter(venv, name, E.VarEntry{ty=initTy}), tenv=tenv}
            end
        | trdec(A.TypeDec tydecs) =
            let
              fun trtydec({name, ty, pos}, {venv, tenv}) =
                {venv=venv, tenv=S.enter(tenv, name, transTy(tenv, ty))}
            in
              foldl trtydec {venv=venv, tenv=tenv} tydecs
            end
        | trdec(A.ClassDec{name, parent, fields, pos}) =
          {venv=venv, tenv=tenv} (* TODO *)
    in
      trdec dec
    end

  and transTy(tenv, ty) =
    let
      fun trty(A.NameTy(name, pos)) =
            (case S.look(tenv, name)
              of SOME(ty) => ty
               | NONE =>
                (error pos ("unknown type '" ^ S.name name ^ "'");
                T.UNIT))
        | trty(A.RecordTy fields) =
          T.UNIT (* TODO *)
        | trty(A.ArrayTy(name, pos)) =
          T.UNIT (* TODO *)
    in
      trty ty
    end

  fun transProg(exp) =
    (transExp(E.base_venv, E.base_tenv, exp); ())

end
