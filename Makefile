default:
	make diagram
	pdf-slatex red-black-pearl.tex
	bibtex red-black-pearl
	pdf-slatex red-black-pearl.tex
	pdf-slatex red-black-pearl.tex

test:
	raco test red-black.rkt

benchmark:
	raco test --submodule benchmark red-black.rkt

diagram:
	raco test --submodule diagram red-black.rkt

clean:
	rm *.aux *.bbl *.blg *.log *.pdf
