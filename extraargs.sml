structure ExtraArgs:
sig
  val calcArgs: Absyn.exp -> int
end =

struct
  structure A = Absyn
  structure S = Symbol

  (* TODO: calculate escapes for class selfs *)

  val error = ErrorMsg.impossible
  val baseEnv = Symbol.empty

  type depth = int
  type escEnv = (depth * bool ref) Symbol.table

  fun traverseVar(env:escEnv, d:depth, s:Absyn.var, count):unit =
    let
      fun trvar(A.SimpleVar(name, pos)) =
            ()
        | trvar(A.FieldVar(var, fieldname, pos)) =
            trvar var
        | trvar(A.SubscriptVar(var, exp, pos)) =
            (trvar var;
            traverseExp(env, d, exp, count))
    in
      trvar s
    end

  and traverseExp(env:escEnv, d:depth, s:Absyn.exp, count:int ref):unit =
    let
      fun trexp(A.VarExp var) =
            traverseVar(env, d, var, count)
        | trexp(A.NilExp) =
            ()
        | trexp(A.IntExp i) =
            ()
        | trexp(A.StringExp(str, pos)) =
            ()
        | trexp(A.CallExp{func, args, pos}) =
            (if length args > (!count) then
              count := (length args)
             else ();
            app trexp args)
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
            (traverseVar(env, d, var, count);
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
              traverseExp(env', d, body, count)
            end
        | trexp(A.BreakExp pos) =
            ()
        | trexp(A.LetExp{decs, body, pos}) =
            let
              val env' = traverseDecs(env, d+1, decs, count)
            in
              traverseExp(env', d, body, count)
            end
        | trexp(A.ArrayExp{typ, size, init, pos}) =
            (trexp size;
            trexp init)
        | trexp(A.MethodExp{var, name, args, pos}) =
            (if length args > (!count) then
              count := (length args)
             else ();
            app trexp args)
        | trexp(A.NewExp(name, pos)) =
            ()
    in
      trexp s
    end

  and traverseDec(env:escEnv, d:depth, s:Absyn.dec, count):escEnv =
    let
      fun trdec(A.FunctionDec fundecs) =
            let
              fun trFun({name, params, levelargs, result, body, pos}, env) =
                let
                  fun trparam({name, escape, typ, pos}, env) =
                    (escape := false;
                    S.enter(env, name, (d+1, escape)))
                  val env' = foldl trparam env params
                in
                  traverseExp(env', d+1, body, levelargs);
                  env'
                end
            in
              foldl trFun env fundecs
            end
        | trdec(A.VarDec{name, escape, typ, init, pos}) =
            let
              val env' = S.enter(env, name, (d, escape))
            in
              escape := false;
              traverseExp(env, d, init, count);
              env'
            end
        | trdec(A.TypeDec decs) =
            env
        | trdec(A.ClassDec{name, parent, attributes, pos}) =
            traverseDecs(env, d, attributes, count)
    in
      trdec s
    end

  and traverseDecs(env:escEnv, d:depth, s:Absyn.dec list, count):escEnv =
    let
      fun trdecs(dec, env) =
        traverseDec(env, d+1, dec, count)
    in
      foldl trdecs env s
    end

  fun calcArgs(exp) =
    let
      val a = ref 0
    in
      traverseExp(baseEnv, 0, exp, a);
      !a
    end
end

