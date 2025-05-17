# Makefile for running soundness checks

# Default target
.PHONY: soundness

# Soundness check target
soundness:
	@if [ -z "$(name)" ]; then \
		echo "Error: 'name' parameter is required. Usage: make soundness name=file.bpl"; \
		exit 1; \
	fi
	bash ~/Documents/boogie.sh $(name) -proverLog:$(name).smt2
	z3.exe trace=true proof=true trace-file-name=$(name).smt2.log $(name).smt2