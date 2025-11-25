TITLE=Abstract Algebra
FILES := Group.Def Group.Basic Group.DefHom Group.HomBasic \
	Group.DefSubgroup

default: $(FILES:%=html/%.html)
	cp html/Agda.css _build/
	uv run fix-links.py
	rm -f _tmp/*.metadata.json
	raco tr build

.SECONDEXPANSION:
html/%.md: src/$$(subst .,/,%).lagda.md
	agda --html --html-highlight=code $<

html/%.html: html/%.md
	pandoc -f markdown -t html $< > $@

deploy:
	cd _build; vercel --prod
