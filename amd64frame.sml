structure Amd64Frame : FRAME =
struct
  type frame = {name: Temp.label, formals: bool list, locals: int ref}
  datatype access = InFrame of int
                  | InReg of Temp.temp
  datatype frag = PROC of {body: Tree.stm, frame: frame}
                | STRING of Temp.label * string

  val wordsize = 8

  val rsp = Temp.newTemp() (* stack pointer *)
  val rax = Temp.newTemp() (* return value *)

  val rdi = Temp.newTemp() (* argument #1 *)
  val rsi = Temp.newTemp() (* argument #2 *)
  val rdx = Temp.newTemp() (* argument #3 *)
  val rcx = Temp.newTemp() (* argument #4 *)
  val r8 = Temp.newTemp() (* argument #5 *)
  val r9 = Temp.newTemp() (* argument #6 *)

  val r10 = Temp.newTemp()
  val r11 = Temp.newTemp()
  val r12 = Temp.newTemp()
  val r13 = Temp.newTemp()
  val r14 = Temp.newTemp()
  val r15 = Temp.newTemp()

  val rbp = Temp.newTemp()
  val rbx = Temp.newTemp()

  val FP = rsp
  val RA = rax

  val registers = ["rsp", "rax", "rbx", "rcx", "rdx", "rsi", "rdi", "rbp", "r8",
                   "r9", "r10", "r11", "r12", "r13", "r14", "r15" ]
  val registerTemps = [rsp, rax, rbx, rcx, rdx, rsi, rdi, rbp, r8,
                       r9, r10, r11, r12, r13, r14, r15]

  val argRegs = [rdi, rsi, rdx, rcx, r8, r9]
  val calleeSaves = [rbx, r12, r13, r14, r15]
  val callerSaves = [rax, r10, r11]
  val specialRegs = [rsp, rbp]

  val colorables = calleeSaves @ callerSaves

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
