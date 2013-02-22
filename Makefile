default:
	make diagram
	pdflatex red-black-pearl.tex

test:
	raco test red-black.rkt

benchmark:
	raco test --submodule benchmark red-black.rkt

diagram:
	raco test --submodule diagram red-black.rkt
