structure Run =
struct
  fun main(prog_name, args) =
    (* Run this program with the name of a tiger file as an argument *)
    let
      val _ = print "\n## Lexical Analysis\n";
      val parsed = Parse.parse ("test.tig")
    in
      print "\n## Abstract Syntax Tree\n";
      PrintAbsyn.print(TextIO.stdOut, parsed);
      print "\n## Type checking\n";
      Semant.transProg(parsed);
      print "\n## Tree Form\n";
      let
        val fragments = Translate.getResult()
        val first =
          case hd fragments
            of Amd64Frame.PROC{body, frame} => body
             | Amd64Frame.STRING _ => Tree.EXP(Tree.CONST 0)
      in
        Printtree.printtree(TextIO.stdOut, first)
      end;
      print "\n";
      0
    end
    handle Fail msg =>
      (print ("\n## Compilation error\n" ^ msg ^ "\n");
      1)
end
