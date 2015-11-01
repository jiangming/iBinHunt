NAME := howto

CHAPTERS := irformulagen.tex stp.tex utils.tex

all: $(NAME).pdf

$(NAME).dvi: $(NAME).tex $(CHAPTERS)
	latex $(NAME).tex
	latex $(NAME).tex

$(NAME).pdf: $(NAME).dvi
	dvipdf $<

clean:
	-rm -f $(NAME).dvi $(NAME).pdf $(NAME).aux $(NAME).out $(NAME).log

