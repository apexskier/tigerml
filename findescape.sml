structure FindEscape:
sig
  val findEscape: Absyn.exp -> unit
end =

struct
  structure A = Absyn

  type depth = int
  type escEnv = (depth * bool ref) Symbol.table

  fun traverseVar(env:escEnv, d:depth, s:Absyn.var):unit =
    let
      fun trvar(A.SimpleVar(name, pos)) =
            ()
        | trvar(A.FieldVar(var, fieldname, pos)) =
            ()
        | trvar(A.SubscriptVar(var, exp, pos)) =
            ()
    in
      trvar s
    end

  fun traverseExp(env:escEnv, d:depth, s:Absyn.exp):unit =
    let
      fun trexp(A.VarExp var) =
            ()
        | trexp(A.NilExp) =
            ()
        | trexp(A.IntExp i) =
            ()
        | trexp(A.StringExp(str, pos)) =
            ()
        | trexp(A.CallExp{func, args, pos}) =
            ()
        | trexp(A.OpExp{left, oper, right, pos}) =
            ()
        | trexp(A.RecordExp{fields, typ, pos}) =
            ()
        | trexp(A.SeqExp exps) =
            ()
        | trexp(A.AssignExp{var, exp, pos}) =
            ()
        | trexp(A.IfExp{test, then', else', pos}) =
            ()
        | trexp(A.WhileExp{test, body, pos}) =
            ()
        | trexp(A.ForExp{var, escape, lo, hi, body, pos}) =
            ()
        | trexp(A.BreakExp pos) =
            ()
        | trexp(A.LetExp{decs, body, pos}) =
            ()
        | trexp(A.ArrayExp{typ, size, init, pos}) =
            ()
        | trexp(A.MethodExp{var, name, args, pos}) =
            ()
        | trexp(A.NewExp(name, pos)) =
            ()
    in
      trexp s
    end

  fun traverseDec(env:escEnv, d:depth, s:Absyn.dec):unit =
    let
      fun trdec(A.FunctionDec fundecs) =
            ()
        | trdec(A.VarDec{name, escape, typ, init, pos}) =
            ()
        | trdec(A.TypeDec list) =
            ()
        | trdec(A.ClassDec{name, parent, fields, pos}) =
            ()
    in
      trdec s
    end

  fun traverseDecs(env:escEnv, d:depth, s:Absyn.dec list):unit =
    let
      fun trdecs(dec) =
        traverseDec(env, d+1, dec)
    in
      app trdecs s
    end

  fun findEscape(exp) =
    let
      val baseEnv = Symbol.empty
    in
      traverseExp(baseEnv, 0, exp)
    end
end
