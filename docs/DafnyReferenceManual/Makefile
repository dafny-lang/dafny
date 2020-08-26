XELATEX=/usr/local/texlive/2020/bin/x86_64-darwin/xelatex

all: options
	./concat DafnyRef.md
	cat DafnyRefZ.md | sed -e '/numbered toc/d' -e '/:toc/d' -e '/PDFOMIT/d'  -e 's/<!--PDF NEWPAGE-->/\\newpage/' | pandoc --toc --number-sections --syntax-definition="../KDESyntaxDefinition/dafny.xml"  --highlight-style=../KDESyntaxDefinition/dafny.theme --pdf-engine=${XELATEX} -H head.tex -B header.tex -V colorlinks=true -t pdf -o DafnyRef.pdf

tex:
	cat DafnyRef.md | sed -e '/numbered toc/d' -e '/:toc/d' -e '/PDFOMIT/d'  -e 's/<!--PDF NEWPAGE-->/\\newpage/' | ./pandoc --toc --pdf-engine=${XELATEX} --number-sections -H head.tex -B header.tex -t latex > DafnyRef.tex

options:
	echo '```' > ../_includes/Options.txt
	../../Binaries/dafny -help | tr -d '\r' | grep -v 'Error: ' >> ../_includes/Options.txt
	echo '```' >> ../_includes/Options.txt

clean:
	@-rm -f DafnyRef.pdf
