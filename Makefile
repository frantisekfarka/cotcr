# Makefile for CoTCR
# Authors: Frantisek Farka

AGDA=agda
GIT=git
SRC=src
STDLIB=standard-library

configure:
	$(GIT) config user.name "Travis CI"
	$(GIT) config user.email "$(COMMIT_AUTHOR_EMAIL)"

doc :	configure
	$(GIT) remote set-branches --add origin gh-pages
	$(GIT) fetch origin gh-pages
	$(GIT) checkout gh-pages
	$(GIT) checkout master -- src
	echo "-- commit:  $(TRAVIS_COMMIT)" >> src/cotcr.agda
	$(AGDA) --html -i $(SRC) -l $(STDLIB) src/cotcr.agda
	$(GIT) add html
	$(GIT) commit -m'auto-generated GH-pages doc'
	$(GIT) checkout -f master





