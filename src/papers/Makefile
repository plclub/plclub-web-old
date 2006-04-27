B2HFLAGS = -dl \
	   -s bold-title \
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

MV=mv
BIBS=bcp.bib geoffw.bib jnf.bib weirich.bib zdancewic.bib

.DELETE_ON_ERROR: $(BIBS)

plclub.html: $(BIBS) Makefile
	bib2bib -s -r -oc plclub.keys -ob merged.bib -c 'bcp:"yes"|plclub:"yes"' $(BIBS)
	bibtex2html -o plclub $(B2HFLAGS) -citefile plclub.keys ./merged.bib
	-$(RM) ./merged.bib

bcp.bib:
	-$(RM) $@
	wget http://www.cis.upenn.edu/~bcpierce/papers/bcp.bib
	bib2bib -ob $@-tmp -c 'not($$key = "poplmark") and not($$key = "AITR-474")' $@
	$(MV) $@-tmp $@

geoffw.bib:
	-$(RM) geoffw.bib
	wget http://www.cis.upenn.edu/~geoffw/research/papers/geoffw.bib

jnf.bib:
	-$(RM) jnf.bib
	wget http://www.cis.upenn.edu/~jnfoster/papers/jnf.bib

weirich.bib:
	-$(RM) $@
	wget http://www.cis.upenn.edu/~sweirich/weirich.bib

zdancewic.bib:
	-$(RM) $@
	wget http://www.cis.upenn.edu/~stevez/papers/zdancewic.bib
	bib2bib -ob $@-tmp -c 'not($$key = "ABFF+05")' $@
	$(MV) $@-tmp $@

clean:
	-$(RM) *.bib plclub.keys plclub.html plclub_bib.html
