structure FindEscape:
sig
  val findEscape: Absyn.exp -> unit
end =

struct
  structure A = Absyn
  structure S = Symbol

  (* TODO: calculate escapes for class selfs *)

  val error = ErrorMsg.impossible
  val baseEnv = Symbol.empty

  type depth = int
  type escEnv = (depth * bool ref) Symbol.table

  fun traverseVar(env:escEnv, d:depth, s:Absyn.var):unit =
    let
      fun trvar(A.SimpleVar(name, pos)) =
            (case S.look(env, name)
              of SOME(d', escape) =>
                if !escape = false then
                  if d > d' then
                    escape := true
                  else ()
                else ()
               | NONE =>
                ()) (* An error will be produced in semant *)
        | trvar(A.FieldVar(var, fieldname, pos)) =
            trvar var
        | trvar(A.SubscriptVar(var, exp, pos)) =
            (trvar var;
            traverseExp(env, d, exp))
    in
      trvar s
    end

  and traverseExp(env:escEnv, d:depth, s:Absyn.exp):unit =
    let
      fun trexp(A.VarExp var) =
            traverseVar(env, d, var)
        | trexp(A.NilExp) =
            ()
        | trexp(A.IntExp i) =
            ()
        | trexp(A.StringExp(str, pos)) =
            ()
        | trexp(A.CallExp{func, args, pos}) =
            app trexp args
        | trexp(A.OpExp{left, oper, right, pos}) =
            (trexp left;
            trexp right)
        | trexp(A.RecordExp{fields, typ, pos}) =
            let
              fun trfield(symbol, exp, pos) =
                trexp exp
            in
              app trfield fields
            end
        | trexp(A.SeqExp exps) =
            let
              fun trexp'(exp, pos) =
                trexp exp
            in
              app trexp' exps
            end
        | trexp(A.AssignExp{var, exp, pos}) =
            (traverseVar(env, d, var);
            trexp exp)
        | trexp(A.IfExp{test, then', else', pos}) =
            (trexp test;
            trexp then';
            case else'
              of SOME(el) => trexp el
               | NONE => ())
        | trexp(A.WhileExp{test, body, pos}) =
            (trexp test;
            trexp body)
        | trexp(A.ForExp{var, escape, lo, hi, body, pos}) =
            let
              val env' = S.enter(env, var, (d, escape))
            in
              escape := false;
              trexp lo;
              trexp hi;
              traverseExp(env', d, body)
            end
        | trexp(A.BreakExp pos) =
            ()
        | trexp(A.LetExp{decs, body, pos}) =
            let
              val env' = traverseDecs(env, d+1, decs, false)
            in
              traverseExp(env', d, body)
            end
        | trexp(A.ArrayExp{typ, size, init, pos}) =
            (trexp size;
            trexp init)
        | trexp(A.MethodExp{var, name, args, pos}) =
            app trexp args
        | trexp(A.NewExp(name, pos)) =
            ()
    in
      trexp s
    end

  and traverseDec(env:escEnv, d:depth, s:Absyn.dec, class:bool):escEnv =
    let
      fun trdec(A.FunctionDec fundecs) =
            let
              fun trFun({name, params, result, body, pos}, env) =
                let
                  fun trparam({name, escape, typ, pos}, env) =
                    (escape := false;
                    S.enter(env, name, (d+1, escape)))
                  val env' = foldl trparam env params
                in
                  traverseExp(env', d+1, body);
                  env'
                end
            in
              foldl trFun env fundecs
            end
        | trdec(A.VarDec{name, escape, typ, init, pos}) =
            let
              val env' = S.enter(env, name, (d, escape))
            in
              escape := class;
              traverseExp(env, d, init);
              env'
            end
        | trdec(A.TypeDec decs) =
            env
        | trdec(A.ClassDec{name, parent, attributes, pos}) =
            traverseDecs(env, d, attributes, true)
    in
      trdec s
    end

  and traverseDecs(env:escEnv, d:depth, s:Absyn.dec list, class:bool):escEnv =
    let
      fun trdecs(dec, env) =
        traverseDec(env, d+1, dec, class)
    in
      foldl trdecs env s
    end

  fun findEscape(exp) =
    traverseExp(baseEnv, 0, exp)
end
