EXEC=tigerml
ARCH=x86-linux

main:
	ml-build sources.cm Run.main $(EXEC)

run:
	sml @SMLload $(EXEC).$(ARCH) test.tig && cat test.tig.s
	gcc -g runtime.c test.tig.s

clean:
	rm -f tiger.lex.* tiger.grm.* tigerml.* *.s *.$(ARCH)
