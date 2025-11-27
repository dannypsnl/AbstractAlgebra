FILES := Group.Def Group.Basic Group.DefHom Group.HomBasic \
	Group.DefSubgroup Group.SubgroupBasic

default: $(FILES:%=html/%.html)
	@uv run fix-links.py
	@raco tr build

.SECONDEXPANSION:
html/%.md: src/$$(subst .,/,%).lagda.md
	agda --html --html-highlight=code $<

html/%.html: html/%.md
	pandoc -f markdown -t html $< > $@
	rm -f _tmp/$*.metadata.json

deploy:
	cd _build; vercel --prod
