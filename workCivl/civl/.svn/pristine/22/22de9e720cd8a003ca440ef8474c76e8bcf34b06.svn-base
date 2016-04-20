package edu.udel.cis.vsl.civl.semantics.common;

import java.util.Arrays;

import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.UnaryOperator;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

/***
 * pointer2IntCaster = new UFExtender(this.universe, POINTER_TO_INT_FUNCTION,
 * this.pointerType, universe.integerType(), new Pointer2IntCaster(universe,
 * symbolicUtil, this.pointerType)); int2PointerCaster = new
 * UFExtender(this.universe, INT_TO_POINTER_FUNCTION, universe.integerType(),
 * this.pointerType, new Int2PointerCaster(universe, symbolicUtil,
 * this.pointerType));
 * 
 * @author zmanchun
 *
 */
// int to pointer
public class Int2PointerCaster implements UnaryOperator<SymbolicExpression> {
	private SymbolicUniverse universe;
	private SymbolicConstant int2PointerFunc;
	private SymbolicUtility symbolicUtil;

	public Int2PointerCaster(SymbolicUniverse universe,
			SymbolicUtility symbolicUtil, SymbolicType pointerType) {
		this.universe = universe;
		this.symbolicUtil = symbolicUtil;
		this.int2PointerFunc = universe.symbolicConstant(universe
				.stringObject(CommonEvaluator.INT_TO_POINTER_FUNCTION),
				universe.functionType(Arrays.asList(universe.integerType()),
						pointerType));
	}

	@Override
	public SymbolicExpression apply(SymbolicExpression value) {
		// only good cast for:
		// 1. from 0 to null pointer
		// 2. pointer2Int(x) back to x;
		if (value.isZero())
			value = this.symbolicUtil.nullPointer();
		else {
			SymbolicExpression castedValue = this.symbolicUtil
					.applyReverseFunction(
							CommonEvaluator.POINTER_TO_INT_FUNCTION, value);

			if (castedValue != null)
				value = castedValue;
			else {
				value = universe.apply(this.int2PointerFunc,
						Arrays.asList(value));
			}
		}
		return value;
	}
}
