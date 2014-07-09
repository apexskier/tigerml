structure Types =
struct
  type unique = unit ref

  datatype ty = RECORD of (Symbol.symbol * ty) list * unique
              | NIL
              | INT
              | STRING
              | ARRAY of ty * unique
              | NAME of Symbol.symbol * ty option ref
              | UNIT
              | CLASS of ty option * (Symbol.symbol * attribute) list * unique (* ty must be CLASS *)

  and attribute = CLASSVAR of {ty: ty}
                | METHOD of {formals: ty list, result: ty}
end
