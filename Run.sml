structure Run =
struct
  fun main(prog_name, args) =
    (* Run this program with the name of a tiger file as an argument *)
    (Main.compile("test.tig");
    0)
    handle Fail msg =>
      (print ("\n## Compilation error\n" ^ msg ^ "\n");
      1)
end
