package edu.udel.cis.vsl.civl.model.IF.type;

import java.util.Collection;

import edu.udel.cis.vsl.civl.model.IF.statement.MallocStatement;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;


//TODO: Document!!

public interface CIVLHeapType extends CIVLType {

	int getNumMallocs();

	MallocStatement getMalloc(int index);

	boolean isComplete();

	void complete(Collection<MallocStatement> mallocs,
			SymbolicType dynamicType, SymbolicExpression initialValue,
			SymbolicExpression undefinedValue);

	SymbolicExpression getInitialValue();

	SymbolicExpression getUndefinedValue();

	String getName();

}
