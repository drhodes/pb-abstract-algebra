SHELL = bash
.SHELLFLAGS := -eu -o pipefail -c
MAKEFLAGS += --warn-undefined-variables
MAKEFLAGS += --no-builtin-rules

# -----------------------------------------------------------------------------
# Section: Python

VENV = source venv/bin/activate &&
PY = ${VENV} python3

venv: util/requirements.txt ## establish a virtual environment for python
	python3 -m venv venv && \
	${PY} -m pip install --upgrade pip
	${PY} -m pip install -r util/requirements.txt
	touch venv 

# -----------------------------------------------------------------------------
# Section: Lectures

MACROS=src/macros.html
BUILD=../builds/pb701-build
SITE=../builds/pb701-build/site

LECTURE_BUILD_DIR=${SITE}/lectures

.PHONY: lectures 
lectures: 
	$(shell mkdir -p ${SITE}/lectures)
	mkdir -p ${SITE}
	${VENV} auxml \
	-i ./src/course.html \
	-d ${SITE} \
	-m ./src/macros.html \
	-m ./src/common-macros.html \
	--patchup ./util/patchup.py

.PHONY: media
media: ${SITE}/media
${SITE}/media: media/css/* media/js/* 
	cp -av media ${SITE}

# -----------------------------------------------------------------------------
# Section: Build server
WEBSERVE=./web/webserve
${WEBSERVE}: venv web/main.go
	cd web && go build


# -----------------------------------------------------------------------------
# Section: Deploy

.PHONY: deploy
deploy: venv lectures ${WEBSERVE}
	mkdir -p ${BUILD}/bin
	cp ${WEBSERVE} ${BUILD}/bin/pb701-serve
	rsync -ravP ${BUILD} derek@proofbased.org:~/
	-ssh derek@proofbased.org 'killall pb701-serve'
	-ssh derek@proofbased.org '~/pb701-build/bin/pb701-serve ~/pb701-build/site&'&


# -----------------------------------------------------------------------------
# Section: Remote

.PHONY: kill-remote-webserver
kill-remote-webserver: 
	ssh derek@proofbased.org 'killall pb701-serve'

.PHONY: start-remote-webserver
start-remote-webserver:
	-ssh derek@proofbased.org 'killall pb701-serve'
	-ssh derek@proofbased.org '~/pb701-build/bin/pb701-serve ~/pb701-build/site&'&


# -----------------------------------------------------------------------------
# Section: Local development 

.PHONY: serve
serve: lectures
	${PY} util/serve_livereload.py

# -----------------------------------------------------------------------------
# Section: Cleaning

.PHONY: clean-python
clean-python: 
	py3clean .

.PHONY: clean-build
clean-build: 
	trash ${BUILD}

.PHONY: clean-venv
clean-venv: 
	rm -rf venv

.PHONY: clean-all
clean-all: clean-python clean-build 
