build:
	@echo "[*] Fixing Coq extracted modules"
	@find src -name '*.hs' -exec sed -i -e 's/GHC.Prim/GHC.Types/' {} \;
	@echo "[*] Building with stack"
	@stack build
