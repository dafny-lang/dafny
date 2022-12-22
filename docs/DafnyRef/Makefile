XELATEXF := /usr/local/texlive/2020/bin/x86_64-darwin/xelatex
XELATEXB := /usr/local/texlive/2020basic/bin/x86_64-darwin/xelatex
XELATEX := $(shell (test -x ${XELATEXF} && echo ${XELATEXF}) || (test -x ${XELATEXB} && echo ${XELATEXB}) || echo "xelatex")

all: numbers options features
	./concat DafnyRef.md | sed -e '/numbered toc/d' -e '/:toc/d' -e '/PDFOMIT/d'  -e 's/<!--PDF NEWPAGE-->/\\newpage/' -e 's/<!--.*-->//' | pandoc --citeproc --toc --syntax-definition="../KDESyntaxDefinition/dafny.xml"  --syntax-definition="../KDESyntaxDefinition/grammar.xml" --highlight-style=../KDESyntaxDefinition/dafny.theme --pdf-engine=xelatex --bibliography=DafnyRef.bib --bibliography=krml250.bib --bibliography=poc.bib --bibliography=paper-full.bib --bibliography=references.bib -H head.tex -B header.tex -V colorlinks=true -t pdf -o DafnyRef.pdf

numbers:
	javac Numbers.java && java Numbers -r DafnyRef.md

options:
	echo '```' > OptionsTemp.txt
	../../Scripts/dafny -help | tr -d '\r' | sed -e 's/[ ]+\n/\n/' | grep -v 'Error: ' >> OptionsTemp.txt
	echo '```' >> OptionsTemp.txt
	if [ ! -e Options.txt ]; then cp OptionsTemp.txt Options.txt; fi
	diff -q OptionsTemp.txt Options.txt || ( cp OptionsTemp.txt Options.txt && echo Updated Options.txt )
	rm OptionsTemp.txt

features:
	dotnet run --no-build --project ../../Source/TestDafny/TestDafny.csproj features > FeaturesTemp.md
	if [ ! -e Features.md ]; then cp FeaturesTemp.md Features.md; fi
	diff -q FeaturesTemp.md Features.md || ( cp FeaturesTemp.md Features.md && echo Updated Features.md )
	rm FeaturesTemp.md

clean:
	@-rm -f DafnyRef.pdf
	rm -rf _site

grammar:
	javac GrammarLinks.java && java -cp . GrammarLinks DafnyRef.md
