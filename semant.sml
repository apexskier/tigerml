signature SEMANT =
sig
  val transProg : Absyn.exp -> unit

  type venv = Env.enventry Symbol.table
  type tenv = Types.ty Symbol.table
  type cenv = Env.classentry Symbol.table
  type expty = {exp:Translate.exp, ty:Types.ty}

  val transVar : venv * tenv * cenv * Absyn.var * Translate.level * Env.classentry option -> expty
  val transExp : venv * tenv * cenv * Absyn.exp * Translate.level * Temp.label * Env.classentry option -> expty
  val transDec : venv * tenv * cenv * Absyn.dec * Translate.exp list * Translate.level * Env.classentry option -> {venv:venv, tenv:tenv, cenv:cenv, exps:Translate.exp list} * Env.classentry option
  val transDecs : venv * tenv * cenv * Absyn.dec list * Translate.level * Env.classentry option -> {venv:venv, tenv:tenv, cenv:cenv, exps:Translate.exp list} * Env.classentry option
  val transTy : tenv * Absyn.ty -> Types.ty
end

structure Semant : SEMANT =
struct
  structure A = Absyn
  structure E = Env
  structure T = Types
  structure Tr = Translate
  structure S = Symbol

  val count = ref 0 (* DEBUG *)

  val error = ErrorMsg.error
  val errExpty = {exp=Tr.emptyEx, ty=T.UNIT}
  val noBreak = Temp.newLabel()

  (* val reservedWords = ["self"] *) (* TODO: decide whether self should be a reserved word *)

  type venv = E.enventry S.table
  type tenv = T.ty S.table
  type cenv = E.classentry S.table
  type expty = {exp: Tr.exp, ty: T.ty}

  (* Utility functions *)
  fun actTy(T.NAME(name, ty)) =
    (case !ty
      of NONE => (error 0 ("unknown name " ^ S.name name); T.UNIT)
       | SOME t => actTy t)
    | actTy t = t

  fun getSym(s: S.symbol, _) = s

  fun getExp({exp, ty}) = exp

  fun idx(item, ls) =
    let
      fun idx'(m, nil) = 0
        | idx'(m, h::t) = if h = item then m else idx'(m+1, t)
    in
      idx'(0, ls)
    end

  fun tyEq(a, b) =
    let val A = actTy a
        val B = actTy b
    in
      if A = B then true
      else
        case A
          of T.NIL =>
            (case B
              of T.RECORD(_, _) => true
               | _ => false)
           | T.RECORD(_, u) =>
            (case B
              of T.RECORD(_, u') => u = u'
               | T.NIL => true
               | _ => false)
           | T.CLASS(_, parent, u) =>
            (case parent
              of SOME(parent) =>
                tyEq(parent, B)
               | NONE => false)
           | _ => false
    end

  fun strTy(ty) =
    case ty
      of T.RECORD _ => "record"
       | T.NIL => "nil"
       | T.INT => "int"
       | T.STRING => "string"
       | T.ARRAY _ => "array"
       | T.NAME _ => "name"
       | T.UNIT => "unit"
       | T.CLASS _ => "class"

  (* Main visible functions *)
  fun transVar(venv, tenv, cenv, var, level, class:E.classentry option) =
    let
      fun trvar(A.SimpleVar(id, pos)) =
            (case S.look(venv, id)
              of SOME(E.VarEntry{access, ty}) =>
                {exp=Tr.simpleVar(access, level), ty=actTy ty}
               | SOME(E.FunEntry{level, label, formals, result}) =>
                 (error pos ("function name used as var: '" ^ S.name id ^ "'");
                 errExpty)
               | NONE =>
                (case class
                  of SOME _ =>
                    transVar(venv, tenv, cenv, A.FieldVar(A.SimpleVar(S.symbol "self", pos), id, pos), level, class)
                   | NONE =>
                    (error pos ("unknown variable '" ^ S.name id ^ "'");
                    errExpty)))
        | trvar(A.FieldVar(var, id, pos)) =
            let
              val {exp=varExp, ty=varTy} = trvar var
            in
              case varTy
                of T.RECORD(fields, _) =>
                    (* look up field *)
                    let
                      val fpos = ref 0
                      fun matchField(field) =
                        (fpos := !fpos + 1;
                        id = getSym field)
                    in
                      case List.find matchField fields
                        of SOME(s, ty) => {exp=Tr.fieldVar{var=varExp, pos=(!fpos - 1)}, ty=ty}
                         | NONE => (
                            error pos ("record field '" ^ S.name id ^ "' not found");
                            errExpty)
                    end
                 | T.CLASS(s, t, u) =>
                    (* generate list of attributes by recursing up inheritance *)
                    (* find a matching class attribute *)
                    (* verify attribute is a variable *)
                    let
                      val class' as E.ClassEntry{parent, attributes} =
                        case class
                          of SOME c => c
                           | NONE =>
                            case S.look(cenv, s)
                              of SOME c => c
                               | NONE => ErrorMsg.impossible "no class found for class type"
                      fun eq(attrname, enventry) =
                        attrname = id
                      fun matchAttr(E.ClassEntry{parent, attributes}) =
                        case parent
                          of SOME parent' =>
                            (case List.find eq (rev attributes) (* TODO: test with class inheritance *)
                              of m as SOME(symbol, entry) => SOME entry
                               | NONE => matchAttr parent')
                           | NONE =>
                            NONE
                      val matchedAttr = matchAttr class'
                    in
                      case matchedAttr
                        of SOME(E.VarEntry{access, ty}) =>
                          let
                            fun getAttrs(class as E.ClassEntry{parent=pclass, attributes=thisAttrs}, baseAttrs) =
                              case pclass
                                of NONE => baseAttrs
                                 | SOME(pclass') =>
                                  let
                                    fun insertAttr(attr as (attrname:S.symbol, enventry:E.enventry), attrs) =
                                      let
                                        fun eq name =
                                          attrname = name
                                      in
                                        if List.exists eq attrs then
                                          attrs
                                        else
                                          attrname :: attrs
                                      end
                                  in
                                    getAttrs(pclass', foldl insertAttr baseAttrs thisAttrs)
                                  end
                            val allattrs = getAttrs(class', nil)
                            val pos = idx(id, allattrs)
                          in
                            {exp=Tr.fieldVar{var=varExp, pos=pos}, ty=actTy ty}
                          end
                         | SOME(E.FunEntry _) =>
                          (error pos ("accessing class method '" ^ S.name id ^ "' as class variable");
                          errExpty)
                         | NONE =>
                          (error pos ("class variable '" ^ S.name id ^ "' not found");
                          errExpty)
                    end
                 | _ => (
                    error pos ("accessing field '" ^ S.name id ^ "' on something not a record or class");
                    errExpty)
            end
        | trvar(A.SubscriptVar(var, exp, pos)) =
            let
              val {exp=varExp, ty=varTy} = trvar var
              val {exp=expExp, ty=expTy} = transExp(venv, tenv, cenv, exp, level, noBreak, class)
            in
              if tyEq(expTy, T.INT) then
                case varTy
                  of T.ARRAY(ty, _) => {exp=Tr.subscriptVar{var=varExp, loc=expExp}, ty=ty}
                   | _ => (error pos "subscripting non-array";
                      errExpty)
              else
                (error pos ("subscripting with non integer");
                errExpty)
            end
    in
      trvar var
    end

  and transExp(venv, tenv, cenv, exp, level, brkAlw, class:E.classentry option) =
    let
      fun trexp(A.VarExp var) =
            transVar(venv, tenv, cenv, var, level, class)
        | trexp(A.NilExp) =
            {exp=Tr.emptyEx, ty=T.NIL}
        | trexp(A.IntExp i) =
            {exp=Tr.intExp(i), ty=T.INT}
        | trexp(A.StringExp(s, pos)) =
            {exp=Tr.stringExp(s), ty=T.STRING}
        | trexp(A.CallExp{func, args, pos}) =
            (case S.look(venv, func)
              of SOME(E.FunEntry{level=funlevel, label, formals, result=resultTy}) =>
                  let
                    fun matchTyGetExp(a, f) =
                      let
                        val {exp=aExp, ty=ty} = trexp a
                      in
                        if tyEq(ty, f) then ()
                        else
                          error pos ("wrong argument type: '" ^ S.name func ^ "'");
                        aExp
                      end
                    val frmsLen = length formals
                    val argsLen = length args
                  in
                    if frmsLen <> argsLen then
                      (error pos ("incorrect number of arguments: found " ^ Int.toString argsLen ^ ", expected " ^ Int.toString frmsLen);
                      errExpty)
                    else
                      {exp=Tr.callExp{name=label,
                                      level=level,
                                      funLevel=funlevel,
                                      args=ListPair.map matchTyGetExp(args, formals)}, ty=resultTy}
                  end
               | SOME(E.VarEntry _) =>
                  (error pos ("attempting to call a regular variable: '" ^ S.name func ^ "'");
                  errExpty)
               | NONE =>
                  (error pos ("unknown function: '" ^ S.name func ^ "'");
                  errExpty))
        | trexp(A.OpExp{left, oper, right, pos}) =
            let
              val {exp=leftExp, ty=lTy} = trexp left
              val {exp=rightExp, ty=rTy} = trexp right
              fun arithmetic() =
                let
                  val _ =
                    if tyEq(T.INT, lTy) then ()
                    else error pos "left side of operator must be int"
                  val _ =
                    if tyEq(T.INT, rTy) then ()
                    else error pos "right side of operator must be int"
                in {exp=Tr.arithExp{oper=oper, left=leftExp, right=rightExp}, ty=T.INT} end
              fun comparison() =
                case lTy
                  of T.INT =>
                    {exp=Tr.compareIntExp{oper=oper, left=leftExp, right=rightExp}, ty=T.INT}
                   | T.STRING =>
                    {exp=Tr.compareStrExp{oper=oper, left=leftExp, right=rightExp}, ty=T.INT}
                   | _ =>
                    (error pos "comparison operands must be integers or strings";
                    errExpty)
              fun comparisoneq() =
                case lTy
                  of T.INT =>
                    {exp=Tr.compareIntExp{oper=oper, left=leftExp, right=rightExp}, ty=T.INT}
                   | T.STRING =>
                    {exp=Tr.compareStrExp{oper=oper, left=leftExp, right=rightExp}, ty=T.INT}
                   | T.RECORD(_, un) =>
                    {exp=Tr.compareRefEqExp(leftExp, rightExp), ty=T.INT}
                   | T.ARRAY(_, un) =>
                    {exp=Tr.compareRefEqExp(leftExp, rightExp), ty=T.INT}
                   | T.NIL =>
                    {exp=Tr.compareNil(), ty=T.INT}
                   | T.CLASS(_, _, un) =>
                    {exp=Tr.compareRefEqExp(leftExp, rightExp), ty=T.INT}
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
            (case S.look(tenv, typ)
              of SOME(T.RECORD(fields', unique)) =>
                let
                  val len = length fields
                  val len' = length fields'
                in
                  if len <> len' then
                    (error pos ("unexpected number of fields: expected " ^ Int.toString len' ^ ", found " ^ Int.toString len);
                    errExpty)
                  else
                    let
                      fun matchField((sym', ty'), (sym, exp, pos)) =
                        let
                          val {exp=expExp, ty=expTy} = trexp exp
                        in
                          (if sym' <> sym then
                            error pos ("unexpected record field name: expected " ^ S.name sym' ^ ", found " ^ S.name sym)
                          else
                            if tyEq(ty', expTy) then ()
                            else
                              error pos ("invalid type for record field '" ^ S.name sym' ^ "'");
                          expExp)
                        end
                      val fieldExps = ListPair.map matchField(fields', fields)
                    in
                      {exp=Tr.recordExp(fieldExps), ty=T.RECORD(fields', unique)}
                    end
                end
               | _ =>
                (error pos ("record type not found: '" ^ S.name typ ^ "'");
                errExpty))
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
                  val exps'' = foldr getexps [] exps @ [lastexp']
                in
                  {exp=Tr.seqExp(exps''), ty=lastty}
                end)
        | trexp(A.AssignExp{var, exp, pos}) =
            let
              val {exp=varExp, ty=varTy} = transVar(venv, tenv, cenv, var, level, class)
              val {exp=expExp, ty=expTy} = trexp exp
            in
              (if tyEq(varTy, expTy) then ()
              else
                error pos "assignment type mismatch";
              {exp=Tr.assignExp(varExp, expExp), ty=T.UNIT})
            end
        | trexp(A.IfExp{test, then'=th, else'=el, pos}) =
            let
              val {exp=testExp, ty=testTy} = trexp test
              val _ =
                if tyEq(T.INT, testTy) then ()
                else error pos "if condition must have int type"
              val {exp=thenExp, ty=thenTy} = trexp th
            in
              case el
                of SOME(elseExp) =>
                  let
                    val {exp=elseEx, ty=elseTy} = trexp elseExp
                  in
                    if tyEq(thenTy, elseTy) then
                      {exp=Tr.ifThenElseExp(testExp, thenExp, elseEx), ty=thenTy}
                    else
                      (error pos "else type doesn't match then in if statement";
                      errExpty)
                  end
                 | NONE =>
                  (if tyEq(T.UNIT, thenTy) then ()
                   else
                     error pos "if then expression must have unit type";
                  {exp=Tr.ifThenExp(testExp, thenExp), ty=T.UNIT})
            end
        | trexp(A.WhileExp{test, body, pos}) =
            let
              val finLab = Temp.newLabel()
              val {exp=testExp, ty=tTy} = trexp test
              val {exp=bodyExp, ty=bTy} = transExp(venv, tenv, cenv, body, level, finLab, class)
              val _ =
                if tyEq(T.INT, tTy) then ()
                else
                  error pos "while condition must have int type"
              val _ =
                if tyEq(T.UNIT, bTy) then ()
                else
                  error pos "while body must have unit type"
            in
              {exp=Tr.whileExp{test=testExp, body=bodyExp, fin=finLab}, ty=T.UNIT}
            end
        | trexp(A.ForExp{var, escape, lo, hi, body, pos}) =
            let
              val finLab = Temp.newLabel()
              val idxAcc = Tr.allocLocal(level)(!escape)
              val {exp=bodyExp, ty=bTy} =
                transExp(S.enter(venv, var, E.VarEntry{access=idxAcc, ty=T.INT}), tenv, cenv, body, level, finLab, class)
              val {exp=loExp, ty=loTy} = trexp lo
              val {exp=hiExp, ty=hiTy} = trexp hi
              val _ =
                if tyEq(T.INT, loTy) then ()
                else
                  error pos "for loop's index must have int type"
              val _ =
                if tyEq(T.INT, hiTy) then ()
                else
                  error pos "for loop's index's upper bound must have int type"
              val _ =
                if tyEq(T.UNIT, bTy) then ()
                else
                  error pos "for loop's body must have unit type"
            in
              {exp=Tr.forExp{var=Tr.simpleVar(idxAcc, level), body=bodyExp, lo=loExp, hi=hiExp, fin=finLab}, ty=T.UNIT}
            end
        | trexp(A.BreakExp pos) =
            if brkAlw <> noBreak then
              {exp=Tr.breakExp(brkAlw), ty=T.UNIT}
            else
              (error pos "break used outside of loop";
              errExpty)
        | trexp(A.LetExp{decs, body, pos}) =
            let
              val ({venv=venv', tenv=tenv', cenv=cenv', exps=exps'}, class) = transDecs(venv, tenv, cenv, decs, level, NONE)
              val {exp=bodyexp, ty=ty} = transExp(venv', tenv', cenv', body, level, brkAlw, class)
            in
              {exp=Tr.letExp(exps', bodyexp), ty=ty}
            end
        | trexp(A.ArrayExp{typ, size, init, pos}) =
            let val {exp=sizeExp, ty=sizeTy} = trexp size
                val {exp=initExp, ty=initTy} = trexp init
                val _ =
                  if tyEq(T.INT, sizeTy) then ()
                  else
                    error pos "array size must have int type"
            in
              case S.look(tenv, typ)
                of SOME(T.ARRAY(ty, unique)) =>
                  if tyEq(initTy, ty) then
                    {exp=Tr.arrayExp{size=sizeExp, init=initExp}, ty=T.ARRAY(initTy, unique)}
                  else
                    (error pos ("init type doesn't match array type: '" ^ S.name typ ^ "'");
                    errExpty)
                 | _ =>
                  (error pos ("unknown array type: '" ^ S.name typ ^ "'");
                  errExpty)
            end
        | trexp(A.MethodExp{var, name, args, pos}) =
            let
              val {exp=varExp, ty} = transVar(venv, tenv, cenv, var, level, class)
            in
              case ty
                of T.CLASS(s, parent, _) =>
                  (* generate list of attributes by recursing up inheritance *)
                  (* find a matching class attribute *)
                  (* verify attribute is a method *)
                  let
                    val class' as E.ClassEntry{parent, attributes} =
                      case class
                        of SOME c => c
                         | NONE =>
                          case S.look(cenv, s)
                            of SOME c => c
                             | NONE =>
                              ErrorMsg.impossible ("class '" ^ S.name s ^ "' of variable not found")
                    fun matchAttr(E.ClassEntry{parent, attributes}) =
                      let
                        fun eq(attrname, enventry) =
                          attrname = name
                      in
                        case parent
                          of SOME(parent') =>
                            (case List.find eq attributes
                              of m as SOME(symbol, entry) => SOME(entry)
                               | NONE => matchAttr parent')
                           | NONE =>
                            NONE
                      end
                    val matchedAttr = matchAttr class'
                  in
                    case matchedAttr
                      of SOME(E.FunEntry{level=funlevel, label, formals, result=resultTy}) =>
                        {exp=Tr.callExp{name=label,
                                        level=level,
                                        funLevel=funlevel,
                                        args=(* self *)varExp::(List.map getExp)(List.map trexp args)}, ty=resultTy}
                       | SOME(E.VarEntry _) =>
                        (error pos ("accessing class variable '" ^ S.name name ^ "' as class method");
                        errExpty)
                       | NONE =>
                        (error pos ("class method '" ^ S.name name ^"' not found");
                        errExpty)
                  end
                 | _ =>
                  (error pos ("attempting to call a method on something not a class instance: '" ^ S.name name ^ "'");
                  errExpty)
            end
        | trexp(A.NewExp(name, pos)) =
            case S.look(tenv, name)
              of SOME(ty) =>
                (case ty
                  of T.CLASS(s, parent, unique) =>
                    let
                      val class =
                        case S.look(cenv, name)
                          of SOME(class) => class
                           | NONE =>
                            (error pos ("class '" ^ S.name name ^ "' not found");
                            case S.look(cenv, S.symbol "Object")
                              of SOME e => e
                               | NONE => ErrorMsg.impossible ("didn't find class '" ^ S.name name ^ "' environment entry"))

                      fun getAttrs(class as E.ClassEntry{parent=pclass, attributes=thisAttrs}, baseAttrs) =
                        case pclass
                          of NONE => baseAttrs
                           | SOME(pclass') =>
                            let
                              fun insertAttr(attr as (attrname:S.symbol, enventry:E.enventry), attrs) =
                                let
                                  fun eq(name, _) =
                                    attrname = name
                                in
                                  if List.exists eq attrs then
                                    attrs
                                  else
                                    let
                                      val attr' =
                                        case enventry
                                          of E.VarEntry{access, ty} =>
                                            (attrname, Tr.simpleVar(access, level))
                                           | E.FunEntry{level=funlevel, label, formals, result} =>
                                            (attrname, Tr.newMethod{name=label, level=level, funLevel=funlevel})
                                    in
                                      attr' :: attrs
                                    end
                                end
                            in
                              (* foldl insertAttr (getAttrs(pclass', baseAttrs)) thisAttrs *)
                              getAttrs(pclass', foldl insertAttr baseAttrs thisAttrs)
                            end
                      val attrs = getAttrs(class, nil)
                      fun getExp(s, exp) = exp
                      val attrs' = map getExp attrs
                    in
                      {exp=Tr.newExp{attrs=attrs', level=level}, ty=ty}
                    end
                   | _ =>
                    (error pos ("attempting to create new instance of non class type: '" ^ S.name name ^ "'");
                    errExpty))
               | NONE =>
                (error pos ("class not found: '" ^ S.name name ^ "'");
                errExpty)
    in
      trexp exp
    end

  and transDecs(venv, tenv, cenv, decs, level, class) =
    let
      fun trdecs(dec, ({venv=venv', tenv=tenv', cenv=cenv', exps=exps'}, class')) =
        transDec(venv', tenv', cenv', dec, exps', level, class')
    in
      foldl trdecs ({venv=venv, tenv=tenv, cenv=cenv, exps=nil}, class) decs
    end

  and transDec(venv, tenv, cenv, dec, exps, level, class) =
    let
      fun trdec(A.FunctionDec fundecs) =
            let
              fun basicFunDec({name, params, result, body, pos}, (funcs, venv, levels, class')) =
                let
                  val label = Temp.newLabel()(* DEBUG: Temp.namedLabel(Symbol.name name) *)
                  fun getEscape{name, escape, typ, pos} =
                    !escape
                  val params' =
                    case class' (* TODO: get escape of self *)
                      of SOME _ =>
                        let
                          val ty = S.symbol "classname"
                        in
                          {name=S.symbol "self", escape=ref true, typ=S.symbol "Object", pos=pos} :: params
                        end
                       | NONE => params
                  val fs =
                    map getEscape params'
                  val newLevel = Tr.newLevel{parent=level, name=label, formals=fs}
                  val resultTy =
                    case result
                      of SOME(s, _) =>
                        (case S.look(tenv, s)
                          of SOME(ty) => ty
                           | NONE =>
                            (error pos ("unknown type in '" ^ S.name name ^ "' function declaration: '" ^ S.name s ^ "'");
                            T.UNIT))
                       | NONE => T.UNIT
                  fun checkParams({name, escape, typ, pos}, params) =
                    case S.look(tenv, typ)
                      of SOME(ty) =>
                        (ty, (name, ty, escape)) :: params
                       | NONE =>
                        (error pos ("unknown type for paramenter '" ^ S.name name ^ "': '" ^ S.name typ ^ "'");
                        params)
                  val paramsEnv = foldr checkParams nil params'
                  val (paramsTys, paramlist) = ListPair.unzip paramsEnv

                  fun testFun({name=name', params, result, body, pos}) =
                    name = name'
                  val numExists = List.filter testFun fundecs
                  val _ =
                    if length numExists > 1 then
                      error pos ("redeclaring function in contiguous function declarations: '" ^ S.name name ^ "'")
                    else ()

                  val fs =
                    case class'
                      of SOME _ => T.CLASS(S.symbol "something", NONE, ref ()) :: paramsTys (* TODO: test *)
                       | NONE => paramsTys
                  val enventry = E.FunEntry{level=level, label=label, formals=fs, result=resultTy}
                  val funcEnv = S.enter(venv, name, enventry)
                  val funcList = ((name, params', result, body, pos), paramlist, resultTy) :: funcs
                  val class'' =
                    case class'
                      of SOME(E.ClassEntry{parent, attributes}) =>
                        SOME(E.ClassEntry{parent=parent, attributes=(name, enventry) :: attributes})
                       | NONE => class'
                in
                  (funcList, funcEnv, newLevel :: levels, class'')
                end
              val (funcList, recEnv, levels, class') = foldr basicFunDec (nil, venv, nil, class) fundecs

              fun checkFunc(((name, params', result, body, pos), formals, resultTy), newLevel) =
                let
                  val accesses = Tr.getAccesses(newLevel, isSome class)
                  fun addParam((name, ty, escape), access, venv') =
                    S.enter(venv', name, E.VarEntry{access=access, ty=ty})
                  val bodyEnv = ListPair.foldl addParam recEnv (formals, accesses)
                  val {exp=bodyExp, ty=bodyTy} = transExp(bodyEnv, tenv, cenv, body, newLevel, noBreak, class)
                in
                  if tyEq(resultTy, bodyTy) then
                    Tr.procEntryExit(newLevel, bodyExp, if tyEq(resultTy, T.UNIT) then false else true)
                  else
                    error pos "function body and result types must match"
                end
              val _ = ListPair.appEq checkFunc (funcList, levels)
            in
              ({venv=recEnv, tenv=tenv, cenv=cenv, exps=exps}, class')
            end
        | trdec(A.VarDec{name, escape, typ, init, pos}) =
            let
              val {exp=initExp, ty=initTy} = transExp(venv, tenv, cenv, init, level, noBreak, class)
              fun eq(a) =
                a = S.name name
              val access = Tr.allocLocal(level)(!escape)
              val initExp' = Tr.varDec{init=initExp, level=level, access=access}
              val enventry = E.VarEntry{access=access, ty=initTy}
              val venv' = case class
                            of SOME _ => venv
                             (* Don't enter into venv, we'll transform these into self.name unless there's an override *)
                             | NONE => S.enter(venv, name, enventry)
              val class' =
                case class
                  of SOME(E.ClassEntry{parent, attributes}) =>
                    SOME(E.ClassEntry{parent=parent, attributes=(name, enventry) :: attributes})
                   | NONE => class
            in
              case typ
                of SOME(tyName, tyPos) =>
                  (case S.look(tenv, tyName)
                    of SOME(ty) =>
                      if tyEq(initTy, ty) then ()
                      else error pos ("variable '" ^ S.name name ^ "' type '" ^ S.name tyName ^ "' doesn't match initialization")
                     | NONE =>
                      error pos ("unknown type '" ^ S.name tyName ^ "' in variable '" ^ S.name name ^ "' declaration"))
                 | NONE =>
                  if initTy = T.NIL then
                    error pos ("initializing non-record variable '" ^ S.name name ^ "' to nil: '" ^ S.name name ^ "'")
                  else
                    ();
              ({venv=venv', tenv=tenv, cenv=cenv, exps=exps @ [initExp']}, class')
            end
        | trdec(A.TypeDec tydecs) =
            let
              fun crInitEnv({name, ty, pos}, tenv) =
                S.enter(tenv, name, T.NIL)
              val initEnv = foldl crInitEnv tenv tydecs
              fun trtydec({name, ty, pos}, {venv, tenv, cenv, exps}) =
                let
                  fun testTy({name=name', ty, pos}) =
                    name = name'
                  val numExists = List.filter testTy tydecs
                  val _ =
                    if length numExists > 1 then
                      error pos ("redeclaring type in contiguous type declarations: '" ^ S.name name ^ "'")
                    else ()

                  val newTy = transTy(initEnv, ty)
                in
                  {venv=venv,
                   tenv=S.enter(tenv, name, newTy),
                   cenv=cenv,
                   exps=exps}
                end
            in
              (foldl trtydec {venv=venv, tenv=tenv, cenv=cenv, exps=exps} tydecs, class)
            end
        | trdec(A.ClassDec{name, parent, attributes, pos}) =
            (* 1. get all attributes(symbol * attribute) and make sure types in attributes exist, typechecking var decs fully
               2. iterate up parents to Object, adding attributes from parents not overridden to head of list
               3. type check method declarations, with a venv augmented with attributes and self *)
            let
              val classTy =
                T.CLASS(name, S.look(tenv, parent), ref ())
              val objectClass =
                case S.look(cenv, S.symbol "Object")
                  of SOME e => e
                   | NONE => ErrorMsg.impossible ("didn't find class '" ^ S.name name ^ "' environment entry")
              val parentClassEntry =
                case S.look(cenv, parent)
                  of SOME parent' => parent'
                   | NONE =>
                    (error pos ("parent class '" ^ S.name parent ^ "' not found");
                    objectClass)

              fun getParentEnv(pclass as E.ClassEntry{parent=pclass', attributes=pattrs}, venv:venv) =
                case pclass'
                  of NONE => venv
                   | SOME(pclass') =>
                    let
                      val venv' = getParentEnv(pclass', venv)
                      fun insertAttr((attrname:S.symbol, enventry:E.enventry), venv) =
                        S.enter(venv, attrname, enventry)
                    in
                      foldl insertAttr venv' pattrs
                    end
              val parentVenv = getParentEnv(parentClassEntry, venv)

              val classTenv = S.enter(tenv, name, classTy)
              val classVenv = parentVenv

              val envclass =
                E.ClassEntry{parent=SOME(parentClassEntry), attributes=nil}

              val ({venv=venv', tenv=tenv', cenv=cenv', exps=exps'}, envclass') =
                transDecs(classVenv, classTenv, cenv, attributes, level, SOME(envclass))

              val envclass'' =
                case envclass'
                  of SOME c => c
                   | NONE => ErrorMsg.impossible "classdec didn't generate environment class"
            in
               ({venv=venv,
                tenv=S.enter(tenv, name, classTy),
                cenv=S.enter(cenv, name, envclass''),
                exps=exps @ exps'}, class)
            end
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
            let
              fun convertField({name, escape, typ, pos}, fields) =
                case S.look(tenv, typ)
                  of SOME(ty) => (name, ty) :: fields
                   | NONE =>
                    (error pos ("unknown type in record field: '" ^ S.name typ ^ "'");
                    fields)
            in
              T.RECORD((foldr convertField [] fields), ref ())
            end
        | trty(A.ArrayTy(name, pos)) =
            (case S.look(tenv, name)
              of SOME(ty) =>
                T.ARRAY(ty, ref ())
               | NONE =>
                (error pos ("unknown array type: '" ^ S.name name ^ "'");
                T.UNIT))
    in
      trty ty
    end

  fun transProg(exp) =
    let
      val _ = FindEscape.findEscape(exp)
      val startLevel = Tr.newLevel{parent=Tr.outermost, name=Temp.namedLabel("tigermain"), formals=[]}
    in
      Tr.procEntryExit(startLevel,
                       getExp(transExp(E.base_venv, E.base_tenv, E.base_cenv, exp, startLevel, noBreak, NONE)),
                       true)
    end
end
