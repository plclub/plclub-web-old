B2HFLAGS = -dl \
	   -s ./bold-title.bst \
           --nodoc -nofooter -noheader --no-abstract -nokeys --no-keywords\
           --named-field slides slides \
           --named-field full 'full version' \
           --named-field short 'short version' \
           --named-field prelim 'preliminary version' \
           --named-field conf 'conference version' \
           --named-field official 'official version' \
           --named-field homepage 'home page' \
           --named-field manuscript 'manuscript' \
           --named-field TR 'tech report' \
           --named-field errata 'errata' \
           --named-field sources 'source code' \
           --reverse-sort --sort-by-date

plclub.html: merged.bib Makefile
	bib2bib -ob /dev/null -oc plclub.keys -c 'bcp:"yes"|plclub:"yes"' merged.bib
	bibtex2html -o plclub $(B2HFLAGS) -citefile plclub.keys merged.bib

merged.bib: bcp.bib geoffw.bib jnf.bib weirich.bib zdancewic.bib
	cat bcp.bib geoffw.bib jnf.bib weirich.bib zdancewic.bib > merged.bib

bcp.bib:
	-$(RM) bcp.bib
	wget http://www.cis.upenn.edu/~bcpierce/papers/bcp.bib

geoffw.bib:
	-$(RM) geoffw.bib
	wget http://www.cis.upenn.edu/~geoffw/research/papers/geoffw.bib

jnf.bib:
	-$(RM) jnf.bib
	wget http://www.cis.upenn.edu/~jnfoster/papers/jnf.bib

weirich.bib:
	-$(RM) weirich.bib
	wget http://www.cis.upenn.edu/~sweirich/weirich.bib

zdancewic.bib:
	-$(RM) zdancewic.bib
	wget http://www.cis.upenn.edu/~stevez/papers/zdancewic.bib

clean:
	-$(RM) *.bib plclub.html
