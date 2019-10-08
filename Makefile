all:
	dune build bin/main.exe && cp _build/default/bin/main.exe ./p4check
jck: 
	dune build bin/main.ml && cp _build/default/bin/main.ml ./p4check