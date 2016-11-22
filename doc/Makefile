LATEX=latexmk -pdf -use-make -e '$$pdflatex=q/xelatex %O %S/'
PAPER=TTT-2017

# latexmk  -bibtex -pdf -e '$$pdflatex=q/xelatex --shell-espace %O %S/' 

paper:
	mkdir -p __build/
	cp *.tex ${PAPER}.bib agda.sty sigplanconf.cls __build/
	cd __build/ && ${LATEX} ${PAPER}.tex
	ln -sf __build/${PAPER}.pdf

clean:
	rm -rf ${PAPER}.pdf __build/
