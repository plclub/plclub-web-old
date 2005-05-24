ERRMSG = $(error USER not defined.  Try "make USER=myname [targets ...]")

all:
	rm -rf dest
	svn export src dest

commit:
	svn commit

update:
	svn update

live:	
	$(if $(USER), ,$(ERRMSG))
	svn commit
	rsync -rulzvtS --delete -e ssh ./dest/ $(USER)@saul.cis.upenn.edu:/mnt/ftp/pub/htdocs/proj/plclub/
