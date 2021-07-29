default: bin/unquote bin/l3hol.run

clean:
	rm -f PPInt.sml
	rm -f lexer.lex.sml
	rm -f bin/l3hol.run
	rm -f bin/unquote
	rm -f lib/sse_float.dynlib

bin/unquote: quote/unquote.sml quote/filter.sml
	@echo "Compiling quotation filter..."
	@polyc -o bin/unquote quote/unquote.sml

lexer.lex.sml: lexgen.sml lexer.lex
	@echo "Making lexer..."
	@echo "LexGen.lexGen \"lexer.lex\"" | poly -q --use "lexgen.sml" > /dev/null

lib/sse_float.dynlib: lib/sse_float.h lib/sse_float.c
	@echo "Making SSE lib..."
	@cc -shared -fPIC lib/sse_float.c -o lib/sse_float.dynlib

bin/l3hol.run: Base.sml Eval.sml Export.sml HolExport.sml ILExport.sml \
         IsabelleExport.sml Lib.sml Parser.sml Main.sml Matches.sml \
         SMLExport.sml \
         Stringmap.sml Stringset.sml \
         lexer.lex.sml \
         lib/sse_float.dynlib \
         lib/IntExtra.sig lib/IntExtra.sml \
         lib/Bitstring.sig lib/Bitstring.sml \
         lib/BitsN.sig lib/BitsN.sml \
         lib/SSE.sig lib/PolySSE.sml lib/FP.sig lib/FP32.sml lib/FP64.sml \
         lib/FPConvert.sig lib/FPConvert.sml \
         lib/L3.sig lib/L3.sml \
         lib/Nat.sig lib/Nat.sml
	@echo "Compiling L3..."
	@poly --script config_script.sml
	@export L3LIBDIR=$(shell pwd -P)/lib && polyc -o bin/l3hol.run Main.sml && echo "L3 successfully built."
