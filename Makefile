# Makefile for CoTCR
# Authors: Frantisek Farka

AGDA=agda
GIT=git
SRC=src
STDLIB=standard-library

doc :
	$(GIT) fetch origin gh-pages
	$(GIT) checkout gh-pages
	$(GIT) checkout master -- src
	$(AGDA) --html -i $(SRC) -l $(STDLIB) src/cotcr.agda
	$(GIT) add html
	$(GIT) commit -m'auto-generated GH-pages doc'
	$(GIT) checkout -f master





