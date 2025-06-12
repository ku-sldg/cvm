# Coq project makefile

# Documentation target.  Type "make DOC=all-gal.pdf" to make PDF.
DOC	?= gallinahtml

# File $(PROJ) contains the list of source files.
# See "man coq_makefile" for its format.
PROJ	= _CoqProject

# Generated makefile
COQMK	= coq.mk

TEMPLATE_REPO = https://github.com/Durbatuluk1701/coq-templates.git
SLDG_OPAM_REPO_PATH = https://github.com/ku-sldg/opam-repo.git
SLDG_OPAM_REPO_BRANCH = main
SLDG_OPAM_REPO_NAME = ku-sldg/opam-repo

META_FILE = meta.yml

COQBIN?=
ifneq (,$(COQBIN))
# add an ending /
COQBIN:=$(COQBIN)/
endif

all:	
	dune build

test: all
	dune test

clean:
	dune clean

# Generates the meta files for the project
meta: 
	TMP=`mktemp -d` && \
	git clone --quiet $(TEMPLATE_REPO) $$TMP && \
	$$TMP/generate.sh

version:
# First, we re-generate the meta files to make sure everything is up to date
	@echo "Generating meta files\n"
	@make meta > /dev/null
# Then, so long as no files are out of date, we proceed
	@echo "Checking for out of date files:\n"
	@(git diff --quiet && git diff --cached --quiet) || \
	(echo "There are files out of sync with git. Please run 'make' to update them, then commit your changes.\n"; \
	exit 1)
# get a version number from the user
# then we update the opam-file-version in the meta file
# and generate the meta files again
# then we check that only the opam and meta files changed
# then we commit the changes
# then we tag the commit with the version number
# then we push the tag
	@echo "Please enter a version number (e.g. 0.1.0):"
	@read VERSION; \
	echo "Version: $$VERSION"; \
	sed -i "s/opam-file-version: \".*\"/opam-file-version: \"$$VERSION\"/" $(META_FILE); \
	echo "Generating meta files for new version\n"; \
	make meta > /dev/null ; \
	echo "Checking that only the opam and meta files changed:\n" ; \
	((git diff --shortstat | grep "2 files changed, 2 insertions(+), 2 deletions(-)" --quiet) || \
	(echo "Someone meta generated more than 2 tracked changes. Please manually inspect what went wrong.\n"; \
	exit 1)) ; \
	echo "Only 2 files (presumably meta.yml and *.opam) changed. Proceeding to commit.\n"; \
	git add $(META_FILE) *.opam ; \
	git commit -m "Version $$VERSION" ; \
	git tag -a v$$VERSION -m "Version $$VERSION" ; \
	git push && git push --tags

publish%:
# First, we set a new version number
	make version
	@echo "\nPublishing to $(SLDG_OPAM_REPO_NAME)\n\n\n"
	@echo "****************************************\nNOTE: Please make sure that the GITHUB TAGGED VERSION and the OPAM TAGGED VERSIONs are the same!\n****************************************\n\n\n"
	opam repo add -a $(SLDG_OPAM_REPO_NAME) $(SLDG_OPAM_REPO_PATH)
	opam publish --repo=$(SLDG_OPAM_REPO_NAME) --target-branch=$(SLDG_OPAM_REPO_BRANCH)

.PHONY:	all meta
