all:
	dune build bin/main.exe && cp _build/default/bin/main.exe ./p4check

release:
	dune build --profile release bin/main.exe && cp _build/default/bin/main.exe ./p4check

