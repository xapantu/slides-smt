all:mid.pdf

mid.pdf: mid.md
	pandoc -t beamer mid.md --filter columnfilter.py -o mid.pdf --bibliography=cite.bib  --tab-stop=20
