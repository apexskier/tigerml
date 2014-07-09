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
            (case B
              of T.RECORD(_, _) => true
               | _ => false)
           | T.RECORD(_, u) =>
            (case B
              of T.RECORD(_, u') => u = u'
               | T.NIL => true
               | _ => false)
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
      if tyEq(ty, req) then ty
      else
        (error pos ("wrong type: expected " ^ strTy);
        ty)
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
                    fun getParent(pname, attrs) =
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
                        case S.look(tenv, pname)
                          of SOME(T.CLASS(parent', pattrs, parentU)) =>
                              (case parent'
                                of SOME p =>
                                  getParent(p, List.filter checkOverride(pattrs) @ attrs)
                                 | NONE =>
                                  attrs)
                           | _ =>
                              (error pos ("parent class not found: '" ^ S.name pname ^ "'");
                              attrs)
                      end
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
                          of T.CLASSVAR{ty} =>
                            {exp=(), ty=ty}
                           | T.METHOD _ =>
                            (error pos ("using class method as class var: '" ^ S.name id ^ "'");
                            errExpty))
                       | NONE =>
                        (error pos ("class attribute (var) not found: '" ^ S.name id ^ "'");
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
                            error pos ("unexpected record field name: expected " ^ Symbol.name sym' ^ ", found " ^ Symbol.name sym)
                          else
                            if tyEq(ty', expTy) then ()
                            else
                              error pos ("invalid type for record field '" ^ Symbol.name sym' ^ "'")
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
              val {exp=_, ty=varTy} = transVar(venv, tenv, var)
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
            let val {exp=bodyExp, ty=bTy} =
                  transExp(S.enter(venv, var, E.VarEntry{ty=T.INT}), tenv, body)
                val {exp=loExp, ty=loTy} = trexp lo
                val {exp=hiExp, ty=hiTy} = trexp hi
                val _ = checkTy(T.INT, loTy, pos)
                val _ = checkTy(T.INT, hiTy, pos)
            in
              {exp=(), ty=checkTy(T.UNIT, bTy, pos)}
            end
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
            let val {exp=sizeExp, ty=sizeTy} = trexp size
                val {exp=initExp, ty=initTy} = trexp init
                val _ = checkTy(T.INT, sizeTy, pos)
            in
              case S.look(tenv, typ)
                of SOME(T.ARRAY(ty, unique)) =>
                  if tyEq(initTy, ty) then
                    {exp=(), ty=T.ARRAY(ty, unique)}
                  else
                    (error pos ("unexpected init type: '" ^ S.name typ ^ "'");
                    {exp=(), ty=T.UNIT})
                 | _ =>
                  (error pos ("unknown array type: '" ^ S.name typ ^ "'");
                  {exp=(), ty=T.UNIT})
            end
        | trexp(A.MethodExp{var, name, args, pos}) =
            let
              val {exp=_, ty} = transVar(venv, tenv, var)
            in
              case ty
                of T.CLASS(parent, attributes, _) =>
                  (* got class attributes *)
                  (* TODO: look at parent attributes *)
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
            let
              fun basicFunDec({name, params, result, body, pos}, (funcs, venv)) =
                let
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
                        (ty, (name, ty)) :: params
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

                  val funcEnv = S.enter(venv, name, E.FunEntry{formals=paramsTys, result=resultTy})
                  val funcList = ((name, params, result, body, pos), paramlist, resultTy) :: funcs
                in
                  (funcList, funcEnv)
                end
              val (funcList, recEnv) = foldr basicFunDec (nil, venv) fundecs

              fun checkFunc((name, params, result, body, pos), formals, resultTy) =
                let
                  fun addParam((name, ty), venv') =
                    S.enter(venv', name, E.VarEntry{ty=ty})
                  val bodyEnv = foldl addParam recEnv formals
                  val {exp=_, ty=bodyTy} = transExp(bodyEnv, tenv, body)
                  val _ = checkTy(resultTy, bodyTy, pos)
                in
                  ()
                end

              val _ = app checkFunc funcList
            in
              {tenv=tenv, venv=recEnv}
            end
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
            (* 1. get all fields (symbol * attribute) and make sure types in attributes exist, typechecking var decs fully
               2. iterate up parents to Object, adding fields from parents not overridden to head of list
               3. type check method declarations, with a venv augmented with fields and self *)
            let
              fun getField(field, attrs) =
                let
                  fun getTy(s) =
                    case S.look(tenv, s)
                      of SOME(ty) =>
                        ty
                       | NONE =>
                        (error pos ("unknown type: '" ^ S.name s ^ "'");
                        T.UNIT)
                in
                  case field
                    of A.ClassVarDec{name, escape, typ, init, pos} =>
                      (case typ
                        of SOME(tys, _) => (name, T.CLASSVAR{ty=getTy(tys)}) :: attrs
                         | NONE =>
                            let
                              (* TODO: should this have access to self? *)
                              val {exp=_, ty=ty} = transExp(venv, tenv, init)
                            in
                              (name, T.CLASSVAR{ty=ty}) :: attrs
                            end)
                     | A.MethodDec methoddecs =>
                      let
                        fun getMethod({name, params, result, body, pos}, attrs) =
                          let
                            fun checkParam{name, escape, typ, pos} =
                              getTy(typ)
                            val formals = map checkParam params
                          in
                            (case result
                              of SOME(tys, _) => (name, T.METHOD{formals=formals, result=getTy(tys)}) :: attrs
                               | NONE =>
                                   (name, T.METHOD{formals=formals, result=T.UNIT}) :: attrs)
                          end
                      in
                        foldl getMethod attrs methoddecs
                      end
                end
              val thisAttrs = foldr getField nil fields

              fun getParent(pname, attrs) =
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
                  case S.look(tenv, pname)
                    of SOME(T.CLASS(parent', pattrs, parentU)) =>
                        (case parent'
                          of SOME p =>
                            getParent(p, List.filter checkOverride(pattrs) @ attrs)
                           | NONE =>
                            attrs)
                     | _ =>
                        (error pos ("parent class not found: '" ^ S.name pname ^ "'");
                        attrs)
                end
              val allAttrs = getParent(parent, thisAttrs)
              (* fun test(s, _) = print ("--- " ^ (S.name s) ^ "\n")
              val _ = app test allAttrs
              val _ = print "-----\n" *)
            in
              (* TODO: 3 *)
              {venv=venv, tenv=S.enter(tenv, name, T.CLASS(SOME(parent), allAttrs, ref ()))}
            end
    in
      trdec dec
    end

  and transMethodDecs(venv, tenv, decs) =
    let
      fun trdecs(dec, {venv, tenv}) =
        transMethodDec(venv, tenv, dec)
    in
      foldl trdecs {venv=venv, tenv=tenv} decs
    end

  and transMethodDec(venv, tenv, dec) =
    let
      fun trdec(A.ClassVarDec{name, escape, typ, init, pos}) =
            transDec(venv, tenv, A.VarDec{name=name, escape=escape, typ=typ, init=init, pos=pos})
        | trdec(A.MethodDec fundecs) =
            transDec(venv, tenv, A.FunctionDec(fundecs))
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
    (transExp(E.base_venv, E.base_tenv, exp); ())

end
