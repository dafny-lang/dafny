all:
	cat DafnyRef.md | sed -e '/numbered toc/d' -e '/:toc/d' -e '/PDFOMIT/d'  -e 's/<!--PDF NEWPAGE-->/\\newpage/' | pandoc --toc --pdf-engine=xelatex --number-sections -B header.tex -t pdf > DafnyRef.pdf
