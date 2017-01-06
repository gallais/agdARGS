LATEX=latexmk -pdf -use-make -e '$$pdflatex=q/xelatex --shell-escape %O %S/'
PAPER=TTT-2017
SLIDES=2017-01-06
# latexmk  -bibtex -pdf -e '$$pdflatex=q/xelatex --shell-espace %O %S/' 

all: paper slides

prepare:
	mkdir -p __build/
	cp *.tex *.bib *.sty *.cls *.png __build/

paper: prepare
	cd __build/ && ${LATEX} ${PAPER}.tex
	ln -sf __build/${PAPER}.pdf

slides: prepare
	cd __build/ && ${LATEX} ${SLIDES}.tex
	ln -sf __build/${SLIDES}.pdf

clean:
	rm -rf ${SLIDES}.pdf ${PAPER}.pdf __build/
