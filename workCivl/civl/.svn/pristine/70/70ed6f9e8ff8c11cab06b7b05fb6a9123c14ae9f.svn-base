package edu.udel.cis.vsl.civl.semantics.common;

import java.util.Arrays;

import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.object.CharObject;

//char to int
public class Char2IntCaster implements CIVLUnaryOperator<SymbolicExpression> {
	private SymbolicUniverse universe;
	private SymbolicConstant char2IntFunc;
	private SymbolicUtility symbolicUtil;

	public Char2IntCaster(SymbolicUniverse universe,
			SymbolicUtility symbolicUtil) {
		this.universe = universe;
		this.symbolicUtil = symbolicUtil;
		this.char2IntFunc = universe.symbolicConstant(
				universe.stringObject(CommonEvaluator.CHAR_TO_INT_FUNCTION),
				universe.functionType(
						Arrays.asList(this.universe.characterType()),
						universe.integerType()));
	}

	@Override
	public SymbolicExpression apply(BooleanExpression context,
			SymbolicExpression value, CIVLType type) {
		if (value.operator() == SymbolicOperator.CONCRETE) {
			CharObject charObj = (CharObject) value.argument(0);

			return this.universe.integer((int) charObj.getChar());
		} else {
			SymbolicExpression castedValue = this.symbolicUtil
					.applyReverseFunction(CommonEvaluator.INT_TO_CHAR_FUNCTION,
							value);

			if (castedValue != null)
				value = castedValue;
			else
				value = universe.apply(this.char2IntFunc, Arrays.asList(value));
		}
		return value;
	}
}
