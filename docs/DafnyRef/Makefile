all: features numbers
	./concat DafnyRef.md | sed -e '/numbered toc/d' -e '/:toc/d' -e '/PDFOMIT/d'  -e 's/<!--PDF NEWPAGE-->/\\newpage/' -e 's/<!--.*-->//' | pandoc --citeproc --toc --syntax-definition="../KDESyntaxDefinition/dafny.xml"  --syntax-definition="../KDESyntaxDefinition/grammar.xml" --highlight-style=../KDESyntaxDefinition/dafny.theme --pdf-engine=tectonic --bibliography=DafnyRef.bib --bibliography=krml250.bib --bibliography=poc.bib --bibliography=paper-full.bib --bibliography=references.bib -H head.tex -B header.tex -V colorlinks=true -t pdf -o DafnyRef.pdf

numbers:
	javac Numbers.java && java Numbers -r DafnyRef.md

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
