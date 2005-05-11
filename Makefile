all:
	echo "This doesn't do anything yet."

commit:
	svn commit

update:
	svn update

live:	
	rsync -av --delete -e ssh ./src/ $(USER)@saul.cis.upenn.edu:/mnt/ftp/pub/htdocs/proj/plclub/
