signature ENV =
sig
  type access
  type ty = Types.ty
  datatype enventry = VarEntry of {ty : ty}
                    | FunEntry of {formals: ty list, result: ty}
  val base_tenv : ty Symbol.table
  val base_venv : enventry Symbol.table
end

structure Env : ENV =
struct

  structure T = Types
  structure S = Symbol

  type access = unit
  type ty = T.ty
  datatype enventry = VarEntry of {ty : ty}
                    | FunEntry of {formals: ty list, result: ty}

  fun enter ((symbol, entry), env) =
    Symbol.enter(env, symbol, entry)

  val base_tenv = S.enter(S.enter(S.enter(S.empty,
                    S.symbol("int"), T.INT),
                    S.symbol("string"), T.STRING),
                    S.symbol("Object"), T.CLASS(nil, ref ()))

  val base_venv = S.enter(S.enter(S.enter(S.enter(S.enter(S.enter(S.enter(S.enter(S.enter(S.enter(S.empty,
                    S.symbol("print"),    FunEntry{formals=[T.STRING], result=T.UNIT}),
                    S.symbol("flush"),    FunEntry{formals=nil, result=T.UNIT}),
                    S.symbol("getchar"),  FunEntry{formals=nil, result=T.STRING}),
                    S.symbol("ord"),      FunEntry{formals=[T.STRING], result=T.INT}),
                    S.symbol("chr"),      FunEntry{formals=[T.INT], result=T.STRING}),
                    S.symbol("size"),     FunEntry{formals=[T.STRING], result=T.INT}),
                    S.symbol("substring"),FunEntry{formals=[T.STRING,T.INT,T.INT], result=T.STRING}),
                    S.symbol("concat"),   FunEntry{formals=[T.STRING,T.STRING], result=T.STRING}),
                    S.symbol("not"),      FunEntry{formals=[T.INT], result=T.INT}),
                    S.symbol("exit"),     FunEntry{formals=[T.INT], result=T.UNIT})

end

