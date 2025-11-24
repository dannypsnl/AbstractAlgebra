TITLE=Abstract Algebra
FILE=Group

default: html/$(FILE).html
	cp html/Agda.css _build/
	raco tr build

html/%.md : src/%.lagda.md
	agda --html --html-highlight=code $<

html/%.html : html/%.md
	echo '<!DOCTYPE HTML><html><head><meta charset="utf-8"><title>$(TITLE)</title><link rel="stylesheet" href="Agda.css"></head>' > $@
	pandoc -f markdown -t html $< >> $@
