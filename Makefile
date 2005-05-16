all:
	rm -rf dest
	svn export src dest

commit:
	svn commit

update:
	svn update

live:	
	svn commit
	rsync -uzvtS --delete -e ssh ./dest/ $(USER)@saul.cis.upenn.edu:/mnt/ftp/pub/htdocs/proj/plclub/
