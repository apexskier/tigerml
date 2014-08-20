structure Amd64Frame : FRAME =
struct
  structure T = Tree

  datatype access = InFrame of int
                  | InReg of Temp.temp
  type frame = {name:Temp.label, formals:bool list, accesses:access list, locals:int ref, entree:T.stm}
  datatype frag = PROC of {body: T.stm, frame: frame}
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
  val DivReg = rdx

  val registers = ["rsp", "rax", "rbx", "rcx", "rdx", "rsi", "rdi", "rbp", "r8",
                   "r9", "r10", "r11", "r12", "r13", "r14", "r15" ]
  val registerTemps = [rsp, rax, rbx, rcx, rdx, rsi, rdi, rbp, r8,
                       r9, r10, r11, r12, r13, r14, r15]

  val argRegs = [rdi, rsi, rdx, rcx, r8, r9]
  val calleeSaves = [rbx, r12, r13, r14, r15]
  val callerSaves = [rax, r10, r11]
  val specialRegs = [rsp, rbp]

  val colorables = calleeSaves @ callerSaves

  fun getAccess(InFrame k) =
        (fn(fp) => T.MEM(T.BINOP(T.PLUS, fp, T.CONST(k * wordsize))))
    | getAccess(InReg t) =
        (fn(Fp) => T.TEMP t)

  (* fun move(reg, var) = T.MOVE(reg, var) *)

  fun seq [] = T.EXP (T.CONST 0)
    | seq [e] = e
    | seq (e :: es) = (T.SEQ (e, (seq es)))

  fun newFrame{name, formals, argspace} =
    let
      val n = length formals (* TODO: deal with arguments overflowing the registers *)
      val l = length argRegs
      val tolong = l > length formals
      val regargs = if tolong then formals else List.take(formals, l)
      val frameargs = if tolong then [] else List.drop(formals, l)
      fun itr(nil, _) = nil
        | itr(arg::rest, offset) =
            if arg then
              InFrame(offset) :: itr(rest, offset + 1)
            else
              InReg(Temp.newTemp()) :: itr(rest, offset)
      val accesses = itr(formals, 0) (* generate instructions to save all the arguments *)
      val regAccesses = if tolong then accesses else List.take(accesses, l)
      val fraAccesses = if tolong then [] else List.drop(accesses, l)
      fun regInstr(access, reg) =
        T.MOVE(getAccess(access)(T.TEMP FP), T.TEMP reg)
      val offset = ref 0
      val argsspace = ref 1
      fun fraInstr(access) =
        (offset := !offset + 1;
        T.MOVE(T.TEMP(hd argRegs),
               T.MEM(T.BINOP(T.PLUS,
                             getAccess(access)(T.TEMP FP),
                             T.CONST((!offset) * wordsize)))))
      val regInstrs = ListPair.map regInstr (regAccesses, argRegs)
      val fraInstrs = if tolong then [] else map fraInstr fraAccesses
      val instrs = regInstrs @ fraInstrs
      val prelocs =
        if argspace > (l - 1) then
          argspace - (l - 1)
        else
          0
    in
      print("locs = "^Int.toString(prelocs)^"\n");
      {name=name, formals=formals, accesses=accesses, locals=ref prelocs, entree=seq instrs}
    end

  and name(f:frame) = #name f

  and formals(f as {name, formals, accesses, locals, entree}) =
    accesses

  fun allocLocal(f as {name, formals=forms, accesses, locals, entree}) escape =
    if escape then
      (locals := !locals + 1;
      InFrame(!locals))
    else
      InReg(Temp.newTemp())

  fun externalCall(name, args) =
    T.CALL(T.NAME(Temp.namedLabel name), args)

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
      (* TODO val saved = map (fn t => T.TEMP t) (RV :: calleeSaves)
      val temps = map (fn t => exp (allocLocal(frame)(true)) (T.TEMP FP)) saved
      val saveRegisters = seq(ListPair.mapEq move (temps, saved))
      val restoreRegisters = seq(ListPair.mapEq move (saved, temps))
      val body' = seq[saveRegisters, body, restoreRegisters] *)
    in
      T.SEQ(entree, body)
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
              "popq \t%r13\n" ^
              "popq \t%r12\n" ^
              "popq \t%rbx\n" ^
              "ret\n"}
    end
end
