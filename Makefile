# Literate-Agda cards now live as src/*.lagda.scrbl (tr scribble prose +
# @agda|{ }| blocks). The build:
#   1. mirror  src/X.lagda.scrbl -> _tmp/mirror/X.agda  (line-preserving)
#   2. agda --html on that mirror -> _tmp/agda-html/X.html (highlighted)
#   3. weave   src + highlight   -> content/track/X.scrbl (prose + @include slices)
#                                   and html/X.N.html (one slice per @agda block)
#   4. fix-links + raco tr build
LAGDA_FILES := $(shell find src -name "*.lagda.scrbl" | sort)
ADDRS := $(LAGDA_FILES:src/%.lagda.scrbl=%)

MIRRORS := $(ADDRS:%=_tmp/mirror/%.agda)
HTMLS   := $(ADDRS:%=_tmp/agda-html/%.html)

default: weave
	@uv run fix-links.py
	@raco tr build

_tmp/mirror/%.agda: src/%.lagda.scrbl
	@raco tangle-lagda mirror $< $@

# Cards import each other, so agda needs every mirror on its include path
# (see _tmp/mirror in AbstractAlgebra.agda-lib) before any --html run.
.SECONDARY:
$(HTMLS): | $(MIRRORS)
_tmp/agda-html/%.html: _tmp/mirror/%.agda
	@mkdir -p _tmp/agda-html
	@agda --html --html-dir=_tmp/agda-html $<

# weave is cheap text-slicing, and a card (content/track/X.scrbl) and its html
# slices (html/X.N.html) are co-products of one weave; re-weave every build so
# the slices are always present and prose edits always land, while the costly
# agda --html step above stays incremental.
.PHONY: weave
weave: $(HTMLS)
	@for a in $(ADDRS); do \
		raco tangle-lagda weave src/$$a.lagda.scrbl _tmp/agda-html/$$a.html content/track/$$a.scrbl; \
	done

deploy: default
	cd _build; vercel --prod
