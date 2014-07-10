signature SEMANT =
sig
  val transProg : Absyn.exp -> unit

  type venv = Env.enventry Symbol.table
  type tenv = Types.ty Symbol.table
  type expty = {exp: unit, ty: Types.ty}

  val transVar : venv * tenv * Absyn.var * Translate.level -> expty
  val transExp : venv * tenv * Absyn.exp * Translate.level * bool -> expty
  val transDec : venv * tenv * Absyn.dec * Translate.level -> {venv: venv, tenv: tenv}
  val transDecs : venv * tenv * Absyn.dec list * Translate.level -> {venv: venv, tenv: tenv}
  val transTy : tenv * Absyn.ty -> Types.ty
end

structure Semant : SEMANT =
struct

  structure A = Absyn
  structure E = Env
  structure T = Types
  structure Tr = Translate
  structure S = Symbol

  val error = ErrorMsg.error
  val errExpty = {exp=(), ty=T.UNIT}

  (* val reservedWords = ["self"] *) (* TODO: decide whether self should be a reserved word *)

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
            (case B
              of T.RECORD(_, _) => true
               | _ => false)
           | T.RECORD(_, u) =>
            (case B
              of T.RECORD(_, u') => u = u'
               | T.NIL => true
               | _ => false)

           | T.CLASS(parent, _, u) =>
            (case parent
              of SOME(parent) =>
                tyEq(B, parent)
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
  fun transVar(venv, tenv, var, level) =
    let
      fun trvar(A.SimpleVar(id, pos)) =
            (case S.look(venv, id)
              of SOME(E.VarEntry{access, ty}) => {exp=(), ty=actTy ty}
               | SOME(E.FunEntry{level, label, formals, result}) =>
                 (error pos ("function name used as var: '" ^ S.name id ^ "'");
                 errExpty)
               | NONE =>
                 (error pos ("unknown variable '" ^ S.name id ^ "'");
                 errExpty))
        | trvar(A.FieldVar(var, id, pos)) =
            (case #ty(trvar var)
              of T.RECORD(fields, _) =>
                  (* look up field *)
                  let
                    fun matchField(field) =
                      id = getSym field
                  in
                    case List.find matchField fields
                      of SOME(_, ty) => {exp=(), ty=ty}
                       | NONE => (
                          error pos ("record field '" ^ S.name id ^ "' not found");
                          errExpty)
                  end
               | T.CLASS(parent, attrs, _) =>
                  let
                    (* generate list of attributes by recursing up inheritance *)
                    fun getParent(T.CLASS(parent', pattrs, parentU), attrs) =
                          let
                            fun checkOverride(pAttrName, _) =
                              let
                                fun matchAttrs(s, _) = s = pAttrName
                              in
                                case List.find matchAttrs attrs
                                  of SOME _ => false
                                   | NONE => true
                              end
                          in
                            case parent'
                              of SOME p =>
                                getParent(p, List.filter checkOverride(pattrs) @ attrs)
                               | NONE =>
                                attrs
                          end
                      | getParent(_, attrs) =
                          (error pos "parent not a class";
                          attrs)
                    val allAttrs =
                      case parent
                        of SOME(p) => getParent(p, attrs)
                         | _ => attrs

                    (* find a matching class attribute *)
                    fun findField(s, ty) = s = id
                    val matchedAttr = List.find findField(allAttrs)
                  in
                    (* verify attribute is a variable *)
                    case matchedAttr
                      of SOME(s, attr) =>
                        (case attr
                          of T.CLASSVAR{ty, access} =>
                            {exp=(), ty=ty}
                           | T.METHOD _ =>
                            (error pos ("using class method as class var: '" ^ S.name id ^ "'");
                            errExpty))
                       | NONE =>
                        (error pos ("class attribute (var) not found: '" ^ S.name id ^ "'");
                        errExpty)
                  end
               | _ => (
                  error pos ("accessing field '" ^ S.name id ^ "' on something not a record or class");
                  errExpty))
        | trvar(A.SubscriptVar(var, exp, pos)) =
            (case #ty(trvar var)
              of T.ARRAY(ty, _) => {exp=(), ty=ty}
               | _ => (error pos "subscripting non-array";
                  errExpty))
    in
      trvar var
    end

  and transExp(venv, tenv, exp, level, brkAlw) =
    let
      fun trexp(A.VarExp var) =
            {exp=(), ty=(#ty(transVar(venv, tenv, var, level)))}
        | trexp(A.NilExp) =
            {exp=(), ty=T.NIL}
        | trexp(A.IntExp i) =
            {exp=(), ty=T.INT}
        | trexp(A.StringExp s) =
            {exp=(), ty=T.STRING}
        | trexp(A.CallExp{func, args, pos}) =
            (case S.look(venv, func)
              of SOME(E.FunEntry{level, label, formals, result=resultTy}) =>
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
                  val _ =
                    if tyEq(T.INT, lTy) then ()
                    else error pos "left side of operator must be int"
                  val _ =
                    if tyEq(T.INT, rTy) then ()
                    else error pos "right side of operator must be int"
                in {exp=(), ty=T.INT} end
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
                   | T.CLASS(_, _, un) => (* TODO *)
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
                          val {exp=_, ty=expTy} = trexp exp
                          val _ = tyEq(ty', expTy)
                        in
                          if sym' <> sym then
                            error pos ("unexpected record field name: expected " ^ S.name sym' ^ ", found " ^ S.name sym)
                          else
                            if tyEq(ty', expTy) then ()
                            else
                              error pos ("invalid type for record field '" ^ S.name sym' ^ "'")
                        end
                    in
                      (ListPair.app matchField(fields', fields);
                      {exp=(), ty=T.RECORD(fields', unique)})
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
                  val _ = foldl getexps [] exps @ [lastexp']
                in
                  {exp=(), ty=lastty}
                end)
        | trexp(A.AssignExp{var, exp, pos}) =
            let
              val {exp=_, ty=varTy} = transVar(venv, tenv, var, level)
              val {exp=_, ty=expTy} = trexp exp
            in
              (if tyEq(varTy, expTy) then ()
              else
                error pos "assignment type mismatch";
              {exp=(), ty=T.UNIT})
            end
        | trexp(A.IfExp{test, then'=th, else'=el, pos}) =
            let
              val {exp=_, ty=testTy} = trexp test
              val _ =
                if tyEq(T.INT, testTy) then ()
                else error pos "if condition must have int type"
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
                  (if tyEq(T.UNIT, thenTy) then ()
                   else
                     error pos "if then expression must have unit type";
                  {exp=(), ty=T.UNIT})
            end
        | trexp(A.WhileExp{test, body, pos}) =
            let
              val {exp=testExp, ty=tTy} = trexp test
              val {exp=bodyExp, ty=bTy} = transExp(venv, tenv, body, level, true)
              val _ =
                if tyEq(T.INT, tTy) then ()
                else
                  error pos "while condition must have int type"
              val _ =
                if tyEq(T.UNIT, bTy) then ()
                else
                  error pos "while body must have unit type"
            in
              {exp=(), ty=T.UNIT}
            end
        | trexp(A.ForExp{var, escape, lo, hi, body, pos}) =
            let
              val idxAcc = Tr.allocLocal(level)(!escape)
              val {exp=bodyExp, ty=bTy} =
                transExp(S.enter(venv, var, E.VarEntry{access=idxAcc, ty=T.INT}), tenv, body, level, true)
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
              {exp=(), ty=T.UNIT}
            end
        | trexp(A.BreakExp pos) =
          if brkAlw then
            {exp=(), ty=T.UNIT}
          else
            (error pos "break used outside of loop";
            errExpty)
        | trexp(A.LetExp{decs, body, pos}) =
            let
              val {venv=venv', tenv=tenv'} = transDecs(venv, tenv, decs, level)
              val {exp=bodyexp, ty=ty} = transExp(venv', tenv', body, level, brkAlw)
            in
              {exp=(), ty=ty}
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
                    {exp=(), ty=T.ARRAY(ty, unique)}
                  else
                    (error pos ("init type doesn't match array type: '" ^ S.name typ ^ "'");
                    {exp=(), ty=T.UNIT})
                 | _ =>
                  (error pos ("unknown array type: '" ^ S.name typ ^ "'");
                  {exp=(), ty=T.UNIT})
            end
        | trexp(A.MethodExp{var, name, args, pos}) =
            let
              val {exp=_, ty} = transVar(venv, tenv, var, level)
            in
              case ty
                of T.CLASS(parent, attributes, _) =>
                  (* got class attributes *)
                  let
                    fun matchAttr(s, _) =
                      s = name
                  in
                    case List.find matchAttr attributes
                      of SOME(_, attr) =>
                        (case attr
                          of T.METHOD{formals, result} =>
                            let
                              val frmsLen = length formals
                              val argsLen = length args
                              fun matchTy(a, f) =
                                let
                                  val {exp=_, ty=ty} = trexp a
                                in
                                  if tyEq(ty, f) then ()
                                  else
                                    error pos ("wrong argument type: '" ^ S.name name ^ "'")
                                end
                            in
                              if frmsLen <> argsLen then
                                (error pos ("incorrect number of arguments: found " ^ Int.toString argsLen ^ ", expected " ^ Int.toString frmsLen);
                                errExpty)
                              else
                                (ListPair.app matchTy(args, formals);
                                {exp=(), ty=result})
                            end
                           | T.CLASSVAR _ =>
                            (error pos ("calling a class variable: '" ^ S.name name ^ "'");
                            errExpty))
                       | NONE =>
                        (error pos ("calling unknown class attribute: '" ^ S.name name ^ "'");
                        errExpty)
                  end
                 | _ =>
                  (error pos ("attempting to call a method on something not a class instance: '" ^ S.name name ^ "'");
                  errExpty)
            end
        | trexp(A.NewExp(name, pos)) =
            (case S.look(tenv, name)
              of SOME(typ) =>
                (case typ
                  of T.CLASS(parent, attrs, unique) =>
                    {exp=(), ty=T.CLASS(parent, attrs, unique)}
                   | _ =>
                    (error pos ("attempting to create new instance of non class type: '" ^ S.name name ^ "'");
                    errExpty))
               | NONE =>
                (error pos ("class not found: '" ^ S.name name ^ "'");
                errExpty))
    in
      trexp exp
    end

  and transDecs(venv, tenv, decs, level) =
    let
      fun trdecs(dec, {venv, tenv}) =
        transDec(venv, tenv, dec, level)
    in
      foldl trdecs {venv=venv, tenv=tenv} decs
    end

  and transDec(venv, tenv, dec, level) =
    let
      fun trdec(A.FunctionDec fundecs) =
            let
              fun basicFunDec({name, params, result, body, pos}, (funcs, venv)) =
                let
                  val newLevel = Tr.newLevel{parent=level, name=Temp.newLabel(), formals=map (fn(_)=>true) params}
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
                  val paramsEnv = foldr checkParams nil params
                  val (paramsTys, paramlist) = ListPair.unzip paramsEnv

                  fun testFun({name=name', params, result, body, pos}) =
                    name = name'
                  val numExists = List.filter testFun fundecs
                  val _ =
                    if length numExists > 1 then
                      error pos ("redeclaring function in contiguous function declarations: '" ^ S.name name ^ "'")
                    else ()

                  val funcEnv = S.enter(venv, name, E.FunEntry{level=level, label=Temp.newLabel(), formals=paramsTys, result=resultTy})
                  val funcList = ((name, params, result, body, pos), paramlist, resultTy) :: funcs
                in
                  (funcList, funcEnv)
                end
              val (funcList, recEnv) = foldr basicFunDec (nil, venv) fundecs

              fun checkFunc((name, params, result, body, pos), formals, resultTy) =
                let
                  val newLevel = Tr.newLevel{parent=level, name=Temp.newLabel(), formals=map (fn(_)=>true) params}
                  fun addParam((name, ty, escape), venv') =
                    S.enter(venv', name, E.VarEntry{access=Tr.allocLocal(newLevel)(!escape), ty=ty})
                  val bodyEnv = foldl addParam recEnv formals
                  val {exp=_, ty=bodyTy} = transExp(bodyEnv, tenv, body, newLevel, false)
                  val _ =
                    if tyEq(resultTy, bodyTy) then ()
                    else
                      error pos "function body and result types must match"
                in
                  ()
                end

              val _ = app checkFunc funcList
            in
              {tenv=tenv, venv=recEnv}
            end
        | trdec(A.VarDec{name, escape, typ, init, pos}) =
            let
              val {exp=initExp, ty=initTy} = transExp(venv, tenv, init, level, false)
              fun eq(a) =
                a = S.name name
            in
              (* if List.exists eq reservedWords then
                (error pos ("'" ^ S.name name ^ "' is a reserved word");
                {venv=venv, tenv=tenv})
              else *)
                case typ
                  of SOME(tyName, tyPos) =>
                    (case S.look(tenv, tyName)
                      of SOME(ty) =>
                        (if tyEq(initTy, ty) then ()
                        else error pos ("variable type '" ^ S.name tyName ^ "' doesn't match initialization");
                        {venv=S.enter(venv, name, E.VarEntry{access=Tr.allocLocal(level)(!escape), ty=ty}), tenv=tenv})
                       | NONE =>
                        (error pos ("unknown type '" ^ S.name tyName ^ "' in variable declaration");
                        {venv=S.enter(venv, name, E.VarEntry{access=Tr.allocLocal(level)(!escape), ty=initTy}), tenv=tenv}))
                   | NONE =>
                    if initTy = T.NIL then
                      (error pos ("initializing non-record variable to nil: '" ^ S.name name ^ "'");
                      {venv=S.enter(venv, name, E.VarEntry{access=Tr.allocLocal(level)(!escape), ty=initTy}), tenv=tenv})
                    else
                      {venv=S.enter(venv, name, E.VarEntry{access=Tr.allocLocal(level)(!escape), ty=initTy}), tenv=tenv}
            end
        | trdec(A.TypeDec tydecs) =
            let
              fun crInitEnv({name, ty, pos}, tenv) =
                S.enter(tenv, name, T.NIL)
              val initEnv = foldl crInitEnv tenv tydecs
              fun trtydec({name, ty, pos}, {venv, tenv}) =
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
                  {venv=venv, tenv=S.enter(tenv, name, newTy)}
                end
            in
              foldl trtydec {venv=venv, tenv=tenv} tydecs
            end
        | trdec(A.ClassDec{name, parent, fields, pos}) =
            (* 1. get all fields (symbol * attribute) and make sure types in attributes exist, typechecking var decs fully
               2. iterate up parents to Object, adding fields from parents not overridden to head of list
               3. type check method declarations, with a venv augmented with fields and self *)
            (case S.look(tenv, parent)
              of SOME(parentTy) =>
                let
                  val selfAccess = Tr.allocLocal(level)(true)
                  fun getParentAttrs(T.CLASS(parent', pattrs, parentU), attrs) = (* should be side effect free *)
                        let
                          fun checkOverride(pAttrName, _) =
                            let
                              fun matchAttrs(s, _) = s = pAttrName
                            in
                              case List.find matchAttrs attrs
                                of SOME _ => false
                                 | NONE => true
                            end
                        in
                          case parent'
                            of SOME p =>
                              getParentAttrs(p, List.filter checkOverride(pattrs) @ attrs)
                             | NONE =>
                              attrs
                        end
                    | getParentAttrs(_, attrs) =
                        (error pos "parent not a class"; (* TODO: only should print once *)
                        attrs)

                  fun genrEnv(attrs) =
                    let
                      fun attrDec((s, attr), venv) =
                        case attr
                          of T.CLASSVAR{ty, access} =>
                            S.enter(venv, s, E.VarEntry{access=access, ty=ty})
                           | T.METHOD{formals, result} =>
                            S.enter(venv, s, E.FunEntry{level=level, label=Temp.newLabel(), formals=formals, result=result})
                    in
                      S.enter(foldl attrDec venv (getParentAttrs(parentTy, attrs)),
                              S.symbol "self",
                              E.VarEntry{access=selfAccess, ty=T.CLASS(SOME(parentTy), attrs, ref ())})
                    end

                  fun getField(field, attrs) =
                    let
                      fun getTy(s) =
                        case S.look(tenv, s)
                          of SOME(ty) => ty
                           | NONE => T.UNIT
                    in
                      case field
                        of A.ClassVarDec{name, escape, typ, init, pos} =>
                            let
                              val venv' = genrEnv(attrs)
                              val _ =
                                transDec(venv', tenv, A.VarDec{name=name, escape=escape, typ=typ, init=init, pos=pos}, level)
                              val ty =
                                case typ
                                  of SOME(tys, _) =>
                                    (print ("----- " ^ S.name tys ^ "\n");
                                    getTy(tys))
                                   | NONE =>
                                    let
                                      val {exp=_, ty=ty} = transExp(venv', tenv, init, level, false)
                                      (* TODO: Shouldn't print output, since this is run twice (also in transdec) *)
                                    in ty end
                              val access = Tr.allocLocal(level)(!escape)
                            in
                              (name, T.CLASSVAR{ty=ty, access=access}) :: attrs
                            end
                         | A.MethodDec methoddecs =>
                          let
                            fun getMethod({name, params, result, body, pos}, attrs) =
                              let
                                fun checkParam{name, escape, typ, pos} =
                                  getTy(typ)
                                val formals = map checkParam params
                              in
                                (case result
                                  of SOME(tys, _) =>
                                    (name, T.METHOD{formals=formals, result=getTy(tys)}) :: attrs
                                   | NONE =>
                                    (name, T.METHOD{formals=formals, result=T.UNIT}) :: attrs)
                              end
                          in
                            foldl getMethod attrs methoddecs
                          end
                    end
                  val thisAttrs = foldl getField nil fields

                  val allAttrs = getParentAttrs(parentTy, thisAttrs)
                  (* DEBUG: fun test(s, _) = print ("--- " ^ (S.name s) ^ "\n")
                  val _ = app test allAttrs
                  val _ = print "-----\n" *)

                  val methodEnv = genrEnv(allAttrs)

                  fun transField(field) =
                    case field
                      of A.ClassVarDec{name, escape, typ, init, pos} =>
                        ()
                       | A.MethodDec methoddecs =>
                        (transDec(methodEnv, tenv, A.FunctionDec methoddecs, level); ())

                  val _ = app transField fields
                in
                  {venv=venv, tenv=S.enter(tenv, name, T.CLASS(SOME(parentTy), allAttrs, ref ()))}
                end
               | NONE =>
                (error pos ("parent type not found: '" ^ S.name parent ^ "'");
                {venv=venv, tenv=tenv}))
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
      val startLevel = Tr.newLevel{parent=Tr.outermost, name=Temp.namedLabel("tigermain"), formals=[]}
    in
      transExp(E.base_venv, E.base_tenv, exp, startLevel, false);
      ()
    end

end
