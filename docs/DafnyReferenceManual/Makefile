all:
	./concat DafnyRef.md
	cat DafnyRefZ.md | sed -e '/numbered toc/d' -e '/:toc/d' -e '/PDFOMIT/d'  -e 's/<!--PDF NEWPAGE-->/\\newpage/' | pandoc --toc --pdf-engine=xelatex --resource-path=".:../_includes" --number-sections -H head.tex -B header.tex -t pdf > DafnyRef.pdf

tex:
	cat DafnyRef.md | sed -e '/numbered toc/d' -e '/:toc/d' -e '/PDFOMIT/d'  -e 's/<!--PDF NEWPAGE-->/\\newpage/' | pandoc --toc --pdf-engine=xelatex --number-sections -H head.tex -B header.tex -t latex > DafnyRef.tex

options:
	echo '```' > ../_includes/Options.txt
	dafny -help | grep -v 'Error: ' >> ../_includes/Options.txt
	echo '```' >> ../_includes/Options.txt
