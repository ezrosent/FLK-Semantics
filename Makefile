IC=./idris
ICNODE=./idris-node
IFLAGS=-p effects
EXECS= FLK_sos FLK_bos

all: $(EXECS)

FLK_sos: Sos_main.idr FLK_sos.idr FLK_ast.idr
	$(IC) Sos_main.idr $(IFLAGS) -o $@

FLK_bos: Bos_main.idr FLK_sos.idr FLK_ast.idr
	$(IC) Bos_main.idr $(IFLAGS) -o $@

clean:
	rm *.ibc $(EXECS)
