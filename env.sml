signature ENV =
sig
  type access
  type ty = Types.ty
  datatype enventry = VarEntry of {access: Translate.access, ty : ty}
                    | FunEntry of {level: Translate.level,
                                   label: Temp.label,
                                   formals: ty list,
                                   result: ty}
  datatype classentry = ClassEntry of {parent: classentry option,
                                       attributes: (Symbol.symbol * enventry) list}
  val base_tenv : ty Symbol.table
  val base_venv : enventry Symbol.table
  val base_cenv : classentry Symbol.table
end

structure Env : ENV =
struct
  structure T = Types
  structure Tr = Translate
  structure S = Symbol

  type access = unit
  type ty = T.ty
  datatype enventry = VarEntry of {access: Tr.access, ty : ty}
                    | FunEntry of {level: Tr.level,
                                   label: Temp.label,
                                   formals: ty list,
                                   result: ty}
  datatype classentry = ClassEntry of {parent: classentry option,
                                       attributes: (S.symbol * enventry) list}

  val base_tenv = S.enter(S.enter(S.enter(S.empty,
                    S.symbol("int"), T.INT),
                    S.symbol("string"), T.STRING),
                    S.symbol("Object"), T.CLASS(S.symbol("Object"), NONE, ref ()))

  val base_venv = S.enter(S.enter(S.enter(S.enter(S.enter(S.enter(S.enter(S.enter(S.enter(S.enter(S.enter(S.empty,
                    S.symbol("print"),    FunEntry{level=Tr.outermost,
                                                   label=Temp.namedLabel "print",
                                                   formals=[T.STRING],
                                                   result=T.UNIT}),
                    S.symbol("printint"),    FunEntry{level=Tr.outermost,
                                                   label=Temp.namedLabel "printint",
                                                   formals=[T.INT],
                                                   result=T.UNIT}),
                    S.symbol("flush"),    FunEntry{level=Tr.outermost,
                                                   label=Temp.namedLabel "flush",
                                                   formals=nil,
                                                   result=T.UNIT}),
                    S.symbol("getchar"),  FunEntry{level=Tr.outermost,
                                                   label=Temp.namedLabel "getchar",
                                                   formals=nil,
                                                   result=T.STRING}),
                    S.symbol("ord"),      FunEntry{level=Tr.outermost,
                                                   label=Temp.namedLabel "ord",
                                                   formals=[T.STRING],
                                                   result=T.INT}),
                    S.symbol("chr"),      FunEntry{level=Tr.outermost,
                                                   label=Temp.namedLabel "chr",
                                                   formals=[T.INT],
                                                   result=T.STRING}),
                    S.symbol("size"),     FunEntry{level=Tr.outermost,
                                                   label=Temp.namedLabel "size",
                                                   formals=[T.STRING],
                                                   result=T.INT}),
                    S.symbol("substring"),FunEntry{level=Tr.outermost,
                                                   label=Temp.namedLabel "substring",
                                                   formals=[T.STRING,T.INT,T.INT],
                                                   result=T.STRING}),
                    S.symbol("concat"),   FunEntry{level=Tr.outermost,
                                                   label=Temp.namedLabel "concat",
                                                   formals=[T.STRING,T.STRING],
                                                   result=T.STRING}),
                    S.symbol("not"),      FunEntry{level=Tr.outermost,
                                                   label=Temp.namedLabel "not",
                                                   formals=[T.INT],
                                                   result=T.INT}),
                    S.symbol("exit"),     FunEntry{level=Tr.outermost,
                                                   label=Temp.namedLabel "exit",
                                                   formals=[T.INT],
                                                   result=T.UNIT})

  val base_cenv = S.enter(S.empty,
                    S.symbol("Object"), ClassEntry{parent=NONE, attributes=nil})
end
