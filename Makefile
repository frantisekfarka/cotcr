# Makefile for CoTCR
# Authors: Frantisek Farka

AGDA=agda
GIT=git
SRC=src
STDLIB=standard-library
DEPLOY_KEY=travis_id_rsa

configure:
	$(GIT) config user.name "Travis CI"
	$(GIT) config user.email "$(COMMIT_AUTHOR_EMAIL)"

doc :	configure
	$(GIT) remote set-branches --add origin gh-pages
	$(GIT) fetch origin gh-pages
	$(GIT) checkout gh-pages
	$(GIT) checkout master -- src
	echo "\n-- commit:  $(TRAVIS_COMMIT)" >> src/cotcr.agda
	$(AGDA) --html -i $(SRC) -l $(STDLIB) src/cotcr.agda
	$(GIT) add html
	$(GIT) commit -m'auto-generated GH-pages doc'
	#ENCRYPTED_KEY_VAR="encrypted_${ENCRYPTION_LABEL}_key"
	#ENCRYPTED_IV_VAR="encrypted_${ENCRYPTION_LABEL}_iv"
	#ENCRYPTED_KEY=${!ENCRYPTED_KEY_VAR}
	#ENCRYPTED_IV=${!ENCRYPTED_IV_VAR}
	#openssl aes-256-cbc -K $(ENCRYPTED_KEY) -iv $(ENCRYPTED_IV) -in $(DEPLOY_KEY).enc -out $(DEPLOY_KEY) -d
	openssl aes-256-cbc -K $(encrypted_57579b36e4b4_key) -iv $(encrypted_57579b36e4b4_iv) -in $(DEPLOY_KEY).enc -out $(DEPLOY_KEY) -d
	chmod 600 $(DEPLOY_KEY)
	sh -c 'eval $$(ssh-agent -s); ssh-add $(DEPLOY_KEY); $(GIT) push git@github.com:frantisekfarka/cotcr.git gh-pages;'
	$(GIT) checkout -f master

