COURSE_ID=pb701
COMMON=../common
include ${COMMON}/makefile/Makefile

.PHONY: notes
notes: 
	$(shell mkdir -p ${SITE})
	rsync -rv material/4220/notes ${SITE}

.PHONY: media
media: ${SITE}/media
${SITE}/media: media/css/* media/js/* notes
	rsync -rv media ${SITE}
