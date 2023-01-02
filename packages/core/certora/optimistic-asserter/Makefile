default: help

PATCH         = applyHarness.patch
CONTRACTS_DIR = ../../contracts
MUNGED_DIR = ./munged
OptimisticAsserter_Origin = ../../contracts/optimistic-asserter/implementation/OptimisticAsserter.sol
OptimisticAsserter_munged = ./munged/OptimisticAsserter.sol
MultiCaller_Origin = ../../contracts/common/implementation/MultiCaller.sol
MultiCaller_munged = ./munged/MultiCall.sol

help:
	@echo "usage:"
	@echo "  make clean:  remove all generated files (those ignored by git)"
	@echo "  make $(MUNGED_DIR): create $(MUNGED_DIR) directory by applying the patch file to $(CONTRACTS_DIR)"
	@echo "  make record: record a new patch file capturing the differences between $(CONTRACTS_DIR) and $(MUNGED_DIR)"

munged:  $(wildcard $(CONTRACTS_DIR)/*.sol) $(PATCH)
	rm -rf $@
	cp -r $(CONTRACTS_DIR) $@
	patch -p0 -d $@ < $(PATCH)

record:
	diff -ruN $(OptimisticAsserter_Origin) $(OptimisticAsserter_munged) | sed 's+\$(OptimisticAsserter_Origin)/++g' | sed 's+$(OptimisticAsserter_munged)++g' > $(PATCH)
	diff -ruN $(MultiCaller_Origin) $(MultiCaller_munged) | sed 's+\$(MultiCaller_Origin)/++g' | sed 's+$(MultiCaller_munged)++g' >> $(PATCH)

clean:
	git clean -fdX
	touch $(PATCH)