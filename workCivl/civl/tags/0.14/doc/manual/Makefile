NAME=civl-manual
SRC=$(NAME).tex
BIB=civl.bib

$(NAME).pdf: $(SRC) part-introduction.tex part-language.tex \
             part-semantics.tex part-tools.tex $(BIB) Makefile \
             ../images/scopeCodeExample.pdf ../images/scopeStateExample.pdf
	pdflatex $(SRC)
	bibtex $(NAME)
	pdflatex $(SRC)
	pdflatex $(SRC)

clean:
	rm -f *.aux *.log *.out *.pdf *.blg *.bbl *.toc
