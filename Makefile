IDRIS := idris
PKG   := powerofpi

.PHONY: build clean clean-all install rebuild doc doc-clean test

all: build

build:
	@$(IDRIS) --build $(PKG).ipkg

clean:
	@$(IDRIS) --clean $(PKG).ipkg
	@find . -name '*.ibc' -delete

clean-all: clean doc-clean

install:
	@$(IDRIS) --install $(PKG).ipkg

rebuild: clean build

docs: build docs-clean
	@$(IDRIS) --mkdoc $(PKG).ipkg \
	&& rm -rf docs >/dev/null \
	&& mv $(PKG)_doc docs

docs-clean:
	@rm -rf $(PKG)_doc docs >/dev/null

test:
	@$(IDRIS) --testpkg $(PKG).ipkg
