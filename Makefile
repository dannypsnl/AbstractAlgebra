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
CARDS   := $(ADDRS:%=content/track/%.scrbl)

default: $(CARDS)
	@uv run fix-links.py
	@raco tr build
	@node build-search-index.mjs _build

_tmp/mirror/%.agda: src/%.lagda.scrbl
	@raco tangle-lagda mirror $< $@

# Cards import each other, so agda needs every mirror on its include path
# (see _tmp/mirror in AbstractAlgebra.agda-lib) before any --html run.
.SECONDARY:
$(HTMLS): | $(MIRRORS)
_tmp/agda-html/%.html: _tmp/mirror/%.agda
	@mkdir -p _tmp/agda-html
	@agda --html --html-dir=_tmp/agda-html $<

content/track/%.scrbl: src/%.lagda.scrbl _tmp/agda-html/%.html
	@mkdir -p content/track
	@raco tangle-lagda weave $< _tmp/agda-html/$*.html $@

deploy: default
	cd _build; vercel --prod
