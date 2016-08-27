# Makefile for CoTCR
# Authors: Frantisek Farka

AGDA=agda
GIT=git
SRC=src
STDLIB=/usr/share/agda-stdlib

doc :
	$(GIT) checkout gh-pages
	$(AGDA) --html -i $(SRC) -i $(STDLIB) src/cotcr.agda
	$(GIT) add html




