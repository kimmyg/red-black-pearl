default:
	make diagram
	pdflatex red-black-pearl.tex
	bibtex red-black-pearl
	pdflatex red-black-pearl.tex
	pdflatex red-black-pearl.tex

test:
	raco test red-black.rkt

benchmark:
	raco test --submodule benchmark red-black.rkt

diagram:
	raco test --submodule diagram red-black.rkt

clean:
	rm *.aux *.bbl *.blg *.log *.pdf
