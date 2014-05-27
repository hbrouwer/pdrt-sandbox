all:
	tidy -i index.html > index.tmp
	mv index.tmp index.html
