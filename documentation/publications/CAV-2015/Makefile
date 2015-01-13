.PHONY: default clean distclean


default: main.pdf


main.pdf: *.tex literature.bib
	pdflatex main && \
	bibtex main && \
	pdflatex main && \
	pdflatex main


clean:
	rm -f *.aux *.log *.bbl *.blg *~ main.pdf

distclean: clean
	rm -f main.pdf
