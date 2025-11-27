# Find all .lagda.md files in src/ and convert paths
LAGDA_FILES := $(shell find src -name "*.lagda.md" | sort)
FILES := $(LAGDA_FILES:src/%.lagda.md=%)
FILES := $(subst /,.,$(FILES))

default: $(FILES:%=html/%.html)
	@uv run fix-links.py
	@raco tr build

.SECONDEXPANSION:
html/%.md: src/$$(subst .,/,%).lagda.md
	agda --html --html-highlight=code $<

html/%.html: html/%.md
	pandoc -f markdown -t html $< > $@
	rm -f _tmp/$*.metadata.json

deploy: default
	cd _build; vercel --prod
