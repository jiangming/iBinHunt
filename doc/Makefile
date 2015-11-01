PAPERNAME=paper
TEXFILES =  *.tex *.sty *.bib

all: 
	echo "Run 'make doc' to build documentation"

doc : $(PAPERNAME).pdf

$(PAPERNAME).pdf : $(TEXFILES) $(PAPERNAME).tex biblio.bib
	latex $(PAPERNAME)
	bibtex $(PAPERNAME)
	latex $(PAPERNAME)
	latex $(PAPERNAME)
	dvips -K -P amz -P cmz -t letter -o $(PAPERNAME).ps \
	$(PAPERNAME)
	ps2pdf $(PAPERNAME).ps $(PAPERNAME).pdf
clean:
	rm -f *.ps *.pdf *.dvi *.aux *.log *.blg *.bbl *~ *.ilg *.idx *.out *.in
