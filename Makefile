all:
	dune build bin/main.exe && cp _build/default/bin/main.exe ./p4check
