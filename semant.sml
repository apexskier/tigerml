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
    let fun trvar(A.SimpleVar(id, pos)) =
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

end
