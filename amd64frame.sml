structure Amd64Frame : FRAME =
struct
  type frame = {name: Temp.label, formals: bool list, locals: int ref}
  datatype access = InFrame of int
                  | InReg of Temp.temp
  datatype frag = PROC of {body: Tree.stm, frame: frame}
                | STRING of Temp.label * string

  val wordsize = 8

  val rsp = Temp.newTemp()
  val rax = Temp.newTemp()

  val FP = rsp
  val RA = rax

  fun newFrame{name, formals} =
    {name=name, formals=formals, locals=ref 0}

  fun name(f:frame) = #name f

  fun formalToAcc(escapes:bool, offset:int ref) =
    if escapes then
      (!offset = !offset + 1;
      InFrame(0 - !offset * wordsize))
    else
      InReg(Temp.newTemp())

  fun formals(f:frame) =
    let
      val escacc = ref 0
      fun formalsAccs[] = []
        | formalsAccs(h::t) =
            formalToAcc(h, escacc) :: formalsAccs(t)
    in
      formalsAccs(#formals f)
    end

  fun allocLocal(f:frame) =
    fn(b) =>
      let
        val escacc = #locals f
      in
        !escacc = !escacc + 1;
        formalToAcc(b, escacc)
      end

  fun exp(InFrame(k)) =
        (fn(fp) => Tree.MEM(Tree.BINOP(Tree.PLUS, fp, Tree.CONST k)))
    | exp(InReg(t)) =
        (fn(Fp) => Tree.TEMP t)

  fun externalCall(name, args) =
    Tree.CALL(Tree.NAME(Temp.namedLabel name), args)

  (* Put a string in memory with a label refering to it *)
  fun string (label, str) =
    (Symbol.name label ^ ": .string \"" ^ str ^ "\"\n.text\n")
end
