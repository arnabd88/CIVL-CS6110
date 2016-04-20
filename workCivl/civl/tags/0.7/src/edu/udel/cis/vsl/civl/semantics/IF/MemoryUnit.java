package edu.udel.cis.vsl.civl.semantics.IF;

import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

public interface MemoryUnit {
	
	enum MemoryUnitKind{
		VARIABLE_OBJECT, HEAP_OBJECT
	}

	MemoryUnitKind memoryUnitKind();
	
	SymbolicExpression reference();
}
