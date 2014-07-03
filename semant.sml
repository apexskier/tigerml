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

structure Semant :> SEMANT =
struct

  structure A = Absyn
  structure E = Env
  structure T = Types
  structure S = Symbol

  val error = ErrorMsg.error

  type venv = E.enventry S.table
  type tenv = T.ty S.table
  type expty = {exp: unit, ty: T.ty}

  fun actTy(T.NAME(name, ty)) =
     (case !ty
        of NONE => (error 0 ("unknown name " ^ S.name name); T.UNIT)
         | SOME t => actTy t)
    | actTy t = t
  fun getSym(s: S.symbol, _) = s

  fun transVar(venv, tenv, var) =
    let
      fun trvar(A.SimpleVar(id, pos)) =
          (case S.look(venv, id)
            of SOME(E.VarEntry{ty}) => {exp=(), ty=actTy ty}
             | SOME(E.FunEntry{formals, result}) =>
                (error pos ("function name used as var: '" ^ S.name id ^ "'");
                {exp=(), ty=T.UNIT})
             | NONE =>
                (error pos ("unknown variable '" ^ S.name id ^ "'");
                {exp=(), ty=T.UNIT}))
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
                        {exp=(), ty=T.UNIT})
                end
             | _ => (
                error pos ("accessing field '" ^ S.name id ^ "' on non-record");
                {exp=(), ty=T.UNIT}))
        | trvar(A.SubscriptVar(var, exp, pos)) =
            ( case #ty(trvar var)
                of T.ARRAY(ty, _) => {exp=(), ty=ty}
                 | _ => (error pos "subscripting non-array";
                          {exp=(), ty=T.UNIT}))
    in
      trvar var
    end

  and transExp(venv, tenv, exp) =
    let
      fun trexp(A.VarExp var) =
          {exp=(), ty=T.UNIT} (* TODO *)
        | trexp(A.NilExp) =
          {exp=(), ty=T.UNIT} (* TODO *)
        | trexp(A.IntExp i) =
          {exp=(), ty=T.UNIT} (* TODO *)
        | trexp(A.StringExp s) =
          {exp=(), ty=T.UNIT} (* TODO *)
        | trexp(A.CallExp{func, args, pos}) =
          {exp=(), ty=T.UNIT} (* TODO *)
        | trexp(A.OpExp{left, oper, right, pos}) =
          {exp=(), ty=T.UNIT} (* TODO *)
        | trexp(A.RecordExp{fields, typ, pos}) =
          {exp=(), ty=T.UNIT} (* TODO *)
        | trexp(A.SeqExp exps) =
          {exp=(), ty=T.UNIT} (* TODO *)
        | trexp(A.AssignExp{var, exp, pos}) =
          {exp=(), ty=T.UNIT} (* TODO *)
        | trexp(A.IfExp{test, then', else', pos}) =
          {exp=(), ty=T.UNIT} (* TODO *)
        | trexp(A.WhileExp{test, body, pos}) =
          {exp=(), ty=T.UNIT} (* TODO *)
        | trexp(A.ForExp{var, escape, lo, hi, body, pos}) =
          {exp=(), ty=T.UNIT} (* TODO *)
        | trexp(A.BreakExp pos) =
          {exp=(), ty=T.UNIT} (* TODO *)
        | trexp(A.LetExp{decs, body, pos}) =
          {exp=(), ty=T.UNIT} (* TODO *)
        | trexp(A.ArrayExp{typ, size, init, pos}) =
          {exp=(), ty=T.UNIT} (* TODO *)
        | trexp(A.MethodExp{var, name, args, pos}) =
          {exp=(), ty=T.UNIT} (* TODO *)
        | trexp(A.NewExp(name, pos)) =
          {exp=(), ty=T.UNIT} (* TODO *)
    in
      trexp exp
    end

  and transDecs(venv, tenv, decs) =
    let
      fun trdecs(dec, {venv, tenv}) =
        transDec(venv, tenv, dec)
    in
      foldr trdecs {venv=venv, tenv=tenv} decs
    end

  and transDec(venv, tenv, dec) =
    let
      fun trdec(A.FunctionDec fundecs) =
          {venv=venv, tenv=tenv}
        | trdec(A.VarDec{name, escape, typ, init, pos}) =
          {venv=venv, tenv=tenv}
        | trdec(A.TypeDec tydecs) =
          {venv=venv, tenv=tenv}
        | trdec(A.ClassDec{name, parent, fields, pos}) =
          {venv=venv, tenv=tenv}
    in
      trdec dec
    end

  and transTy(tenv, ty) =
    let
      fun trty(A.NameTy(name, pos)) =
          T.UNIT
        | trty(A.RecordTy fields) =
          T.UNIT
        | trty(A.ArrayTy(name, pos)) =
          T.UNIT
    in
      trty ty
    end

  fun transProg(exp) =
    ()

end
