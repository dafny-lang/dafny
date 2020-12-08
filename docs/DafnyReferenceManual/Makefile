all: options
	./concat DafnyRef.md | sed -e '/numbered toc/d' -e '/:toc/d' -e '/PDFOMIT/d'  -e 's/<!--PDF NEWPAGE-->/\\newpage/' | pandoc --toc --number-sections --syntax-definition="../KDESyntaxDefinition/dafny.xml"  --highlight-style=../KDESyntaxDefinition/dafny.theme --pdf-engine=xelatex -H head.tex -B header.tex -V colorlinks=true -t pdf -o DafnyRef.pdf

tex:
	./concat DafnyRef.md | sed -e '/numbered toc/d' -e '/:toc/d' -e '/PDFOMIT/d'  -e 's/<!--PDF NEWPAGE-->/\\newpage/' | ./pandoc --toc --pdf-engine=xelatex --number-sections -H head.tex -B header.tex -t latex > DafnyRef.tex

options:
	echo '```' > OptionsTemp.txt
	dafny -help | tr -d '\r' | sed -e 's/[ ]+\n/\n/' | grep -v 'Error: ' >> OptionsTemp.txt
	echo '```' >> OptionsTemp.txt
	if [ ! -e ../_includes/Options.txt ]; then cp OptionsTemp.txt ../_includes/Options.txt; fi
	diff -q OptionsTemp.txt ../_includes/Options.txt || ( cp OptionsTemp.txt ../_includes/Options.txt && echo Updated Options.txt )
	rm OptionsTemp.txt

release: all
	cp DafnyRef.pdf ../DafnyRef/out

clean:
	@-rm -f DafnyRef.pdf
