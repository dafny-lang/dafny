all:
	./concat DafnyRef.md
	cat DafnyRefZ.md | sed -e '/numbered toc/d' -e '/:toc/d' -e '/PDFOMIT/d'  -e 's/<!--PDF NEWPAGE-->/\\newpage/' | pandoc --toc --number-sections --syntax-definition="../KDESyntaxDefinition/dafny.xml"  --highlight-style=tango --pdf-engine=xelatex -H head.tex -B header.tex -V colorlinks=true -t pdf -o DafnyRef.pdf
	##cat DafnyRefZ.md | sed -e '/numbered toc/d' -e '/:toc/d' -e '/PDFOMIT/d'  -e 's/<!--PDF NEWPAGE-->/\\newpage/' | pandoc --toc --pdf-engine=xelatex --resource-path=".:../_includes" --number-sections -H head.tex -B header.tex -t pdf  --syntax-definition="../KDESyntaxDefinition/dafny.xml" --highlight-style=tango --pdf-engine=xelatex -o DafnyRef.pdf

tex:
	cat DafnyRef.md | sed -e '/numbered toc/d' -e '/:toc/d' -e '/PDFOMIT/d'  -e 's/<!--PDF NEWPAGE-->/\\newpage/' | pandoc --toc --pdf-engine=xelatex --number-sections -H head.tex -B header.tex -t latex > DafnyRef.tex
