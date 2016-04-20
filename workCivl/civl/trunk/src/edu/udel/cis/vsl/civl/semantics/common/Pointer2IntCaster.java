package edu.udel.cis.vsl.civl.semantics.common;

import java.util.Arrays;

import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

//pointer to int
public class Pointer2IntCaster implements CIVLUnaryOperator<SymbolicExpression> {
	private SymbolicUniverse universe;
	private SymbolicConstant pointer2IntFunc;
	private SymbolicUtility symbolicUtil;

	public Pointer2IntCaster(SymbolicUniverse universe,
			SymbolicUtility symbolicUtil, SymbolicType pointerType) {
		this.universe = universe;
		this.symbolicUtil = symbolicUtil;
		this.pointer2IntFunc = universe.symbolicConstant(
				universe.stringObject(CommonEvaluator.POINTER_TO_INT_FUNCTION),
				universe.functionType(Arrays.asList(pointerType),
						universe.integerType()));
	}

	@Override
	public SymbolicExpression apply(BooleanExpression context,
			SymbolicExpression value, CIVLType castType) {
		if (this.symbolicUtil.isNullPointer(value))
			value = universe.integer(0);
		else if (!value.type().equals(universe.integerType())) {
			SymbolicExpression castedValue = this.symbolicUtil
					.applyReverseFunction(
							CommonEvaluator.INT_TO_POINTER_FUNCTION, value);

			if (castedValue != null)
				value = castedValue;
			else
				value = universe.apply(this.pointer2IntFunc,
						Arrays.asList(value));
		}
		return value;
	}

}
