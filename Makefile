.PHONY: test Everything.agda clean

OTHEROPTS = -Werror

RTSARGS = +RTS -M6G -A128M -RTS ${OTHEROPTS}

test: Everything.agda
	agda ${RTSARGS} -i. Everything.agda

html: Everything.agda
	agda ${RTSARGS} --html -i. Everything.agda

Everything.agda:
	git ls-tree --full-tree -r --name-only HEAD | grep '^src/[^\.]*.[agda|lagda.org|lagda.md]' | sed -e 's|^src/[/]*|import |' -e 's|/|.|g' -e 's/.lagda.md//' -e 's/.lagda.org//' -e 's/.agda//' -e '/import Everything/d' | LC_COLLATE='C' sort > Everything.agda
	sed -i '1s;^;{-# OPTIONS --guarded #-}\n;' Everything.agda

clean:
	find . -name '*.agdai' -exec rm \{\} \;
