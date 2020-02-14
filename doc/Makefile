update-footer := cat footer-head > footer; date >> footer; cat footer-tail >> footer
mypandoc      := pandoc
mathjax_provider := "https://cdnjs.cloudflare.com/ajax/libs/mathjax/2.7.5/MathJax.js?config=TeX-MML-AM_CHTML"

all: html pdf
# all: html

html: splat.html splat-mon.html

pdf: splat.pdf splat-mon.pdf

splat.html: splat.txt
	$(update-footer)
	$(mypandoc) -s -S\
               -c mypandoc.css\
               -A footer\
               --toc\
               --toc-depth=6\
               --mathjax=$(mathjax_provider)\
               splat.txt\
               -o splat.html

splat.pdf: splat.txt
	$(mypandoc) -s -S\
               -B toc.tex\
               --latex-engine=xelatex\
               splat.txt\
               -o splat.pdf

splat-mon.html: splat-mon.txt
	$(update-footer)
	$(mypandoc) -s -S\
               -c mypandoc.css\
               -A footer\
               --toc\
               --toc-depth=6\
               --mathjax=$(mathjax_provider)\
               splat-mon.txt\
               -o splat-mon.html

splat-mon.pdf: splat-mon.txt
	$(mypandoc) -s -S\
               -B toc.tex\
               --latex-engine=xelatex\
               splat-mon.txt\
               -o splat-mon.pdf

# Delete HTML and PDF files

clean:
	rm -f splat.html
	rm -f splat.pdf
	rm -f splat-mon.html
	rm -f splat-mon.pdf
