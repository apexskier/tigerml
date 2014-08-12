structure Amd64Frame : FRAME =
struct
  datatype access = InFrame of int
                  | InReg of Temp.temp
  type frame = {name:Temp.label, formals:bool list, accesses:access list, locals:int ref, entree:Tree.stm}
  datatype frag = PROC of {body: Tree.stm, frame: frame}
                | STRING of Temp.label * string
  type register = string

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
  val RV = rax

  val registers = ["rsp", "rax", "rbx", "rcx", "rdx", "rsi", "rdi", "rbp", "r8",
                   "r9", "r10", "r11", "r12", "r13", "r14", "r15" ]
  val registerTemps = [rsp, rax, rbx, rcx, rdx, rsi, rdi, rbp, r8,
                       r9, r10, r11, r12, r13, r14, r15]

  val argRegs = [rdi, rsi, rdx, rcx, r8, r9]
  val calleeSaves = [rbx, r12, r13, r14, r15]
  val callerSaves = [rax, r10, r11]
  val specialRegs = [rsp, rbp]

  val colorables = calleeSaves @ callerSaves

  fun exp(InFrame(k)) =
        (fn(fp) => Tree.MEM(Tree.BINOP(Tree.PLUS, fp, Tree.CONST (k * wordsize))))
    | exp(InReg(t)) =
        (fn(Fp) => Tree.TEMP t)

  fun move(reg, var) = Tree.MOVE(reg, var)
  fun seq [] = Tree.EXP (Tree.CONST 0)
    | seq [exp] = exp
    | seq (exp :: exps) = (Tree.SEQ (exp, (seq exps)))

  fun newFrame{name, formals} =
    let
      val n = length formals (* TODO: deal with arguments overflowing the registers *)
      fun itr(nil, _) = nil
        | itr(arg::rest, offset) =
            if arg then
              InFrame(offset) :: itr(rest, offset + 1)
            else
              InReg(let val t = Temp.newTemp() in print ("making new temp "^Temp.makeString t^" newFrame\n"); t end) :: itr(rest, offset)
      val accesses = itr(formals, 0) (* generate instructions to save all the arguments *)
      fun instr(access, reg) =
        Tree.MOVE(exp access (Tree.TEMP FP), Tree.TEMP reg)
      val instrs = ListPair.map instr (accesses, argRegs)
    in
      {name=name, formals=formals, accesses=accesses, locals=ref 0, entree=seq instrs}
    end

  fun name(f:frame) = #name f

  fun formals(f as {name, formals, accesses, locals, entree}) =
    accesses

  fun allocLocal(f:frame) escape =
    let
      val numLocals = #locals f
    in
      if escape then
        (!numLocals = !numLocals + 1;
        InFrame(!numLocals))
      else
        InReg(let val t = Temp.newTemp() in print ("making new temp "^Temp.makeString t^" allocLocal\n"); t end)
    end

  fun externalCall(name, args) =
    Tree.CALL(Tree.NAME(Temp.namedLabel name), args)

  (* Put a string in memory with a label refering to it *)
  fun string (label, str) =
    (Symbol.name label ^ ":\n" ^
    "\t.long " ^ Int.toString(String.size str) ^"\n" ^
    "\t.string \"" ^ String.toCString str ^ "\"\n.text\n")

  val tempMap =
    let
      fun enter((key:Temp.temp, value:string), table) =
        Temp.Table.enter(table, key, value)
    in
      List.foldl enter Temp.Table.empty (ListPair.zip(registerTemps, registers))
    end

  fun procEntryExit1(frame as {name, formals=forms, accesses, locals, entree}, body) =
    let
      (* TODO val saved = map (fn t => Tree.TEMP t) (RV :: calleeSaves)
      val temps = map (fn t => exp (allocLocal(frame)(true)) (Tree.TEMP FP)) saved
      val saveRegisters = seq(ListPair.mapEq move (temps, saved))
      val restoreRegisters = seq(ListPair.mapEq move (saved, temps))
      val body' = seq[saveRegisters, body, restoreRegisters] *)
    in
      Tree.SEQ(entree, body)
    end

  fun procEntryExit2(frame, body) =
    body @ [Assem.OPER{assem="",            (* this just sets some stuff as live, for register allocation *)
            src=[RV] @ calleeSaves @ specialRegs,
            dst=nil, jump=SOME[]}]

  fun procEntryExit3(frame as {name, formals, locals, accesses, entree}, body) =
    let
      val size = ((length formals) + (!locals)) * wordsize
      val space = (size mod 16) + size
    in
      {prolog="\t.text\n" ^
              "\t.globl " ^ Symbol.name name ^ "\n" ^
              Symbol.name name ^ ":\n" ^
              "pushq \t%rbx\n" ^
              "pushq \t%r12\n" ^
              "pushq \t%r14\n" ^
              "pushq \t%r13\n" ^
              "pushq \t%r14\n" ^
              "pushq \t%r15\n" ^
              "pushq \t%rbp\n" ^
              "movq \t%rsp, %rbp\n" ^
              "sub \t$" ^ Int.toString space ^ ", %rsp\n",
       body=body,
       epilog="movq \t%rbp, %rsp\n" ^
              "popq \t%rbp\n" ^
              "popq \t%r15\n" ^
              "popq \t%r14\n" ^
              "popq \t%r12\n" ^
              "popq \t%r13\n" ^
              "popq \t%r14\n" ^
              "popq \t%rbx\n" ^
              "ret\n"}
    end
end
