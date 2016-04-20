package edu.udel.cis.vsl.civl.semantics.common;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.sarl.IF.SARLInternalException;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicSequence;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicCompleteArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicFunctionType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicUnionType;

/**
 * This class extends certain kinds of operations on a type to compound symbolic
 * expressions.
 * 
 * @author siegel
 *
 */
public class UFExtender implements CIVLUnaryOperator<SymbolicExpression> {

	/**
	 * The name you want to use for the uninterpreted functions that will be
	 * created.
	 */
	private StringObject rootName;

	/**
	 * The primary operation which consumes an element of the given input type
	 * and returns something of the given output type. This operation should be
	 * defined everywhere, even if it just applies an uninterpreted functions
	 * most of the time.
	 */
	private CIVLUnaryOperator<SymbolicExpression> rootOperation;

	/**
	 * The input type of the root operation.
	 */
	private SymbolicType inputType;

	/**
	 * The output type of the root operation.
	 */
	private SymbolicType outputType;

	/**
	 * The uninterpreted functions that will be applied when necessary.
	 */
	private Map<SymbolicType, SymbolicConstant> uninterpretedFunctions = new HashMap<>();

	private SymbolicUniverse universe;

	public UFExtender(SymbolicUniverse universe, String rootName,
			SymbolicType inputType, SymbolicType outputType,
			CIVLUnaryOperator<SymbolicExpression> rootFunction) {
		this.rootName = universe.stringObject(rootName);
		this.rootOperation = rootFunction;
		this.inputType = inputType;
		this.outputType = outputType;
		this.universe = universe;
	}

	private SymbolicType newType(SymbolicType type) {
		if (inputType.equals(type))
			return outputType;
		switch (type.typeKind()) {
		case BOOLEAN:
		case CHAR:
		case INTEGER:
		case REAL:
			return type;
		case ARRAY: {
			SymbolicArrayType arrayType = (SymbolicArrayType) type;

			if (arrayType.isComplete())
				return universe.arrayType(newType(arrayType.elementType()),
						((SymbolicCompleteArrayType) arrayType).extent());
			else
				return universe.arrayType(newType(arrayType.elementType()));
		}
		case FUNCTION: {
			SymbolicFunctionType functionType = (SymbolicFunctionType) type;
			List<SymbolicType> newInputTypes = new ArrayList<>();

			for (SymbolicType inputType : functionType.inputTypes()) {
				newInputTypes.add(newType(inputType));
			}
			return universe.functionType(newInputTypes,
					this.newType(functionType.outputType()));
		}
		case TUPLE: {
			SymbolicTupleType tupleType = (SymbolicTupleType) type;
			List<SymbolicType> fieldTypes = new ArrayList<>();

			for (SymbolicType fieldType : tupleType.sequence()) {
				fieldTypes.add(newType(fieldType));
			}
			return universe.tupleType(tupleType.name(), fieldTypes);
		}
		case UNION: {
			SymbolicUnionType unionType = (SymbolicUnionType) type;
			List<SymbolicType> fieldTypes = new ArrayList<>();

			for (SymbolicType fieldType : unionType.sequence()) {
				fieldTypes.add(newType(fieldType));
			}
			return universe.unionType(unionType.name(), fieldTypes);
		}
		case MAP:// TODO
		case SET:
			// TODO
		default:
			throw new SARLInternalException("unreachable");
		}
	}

	@Override
	public SymbolicExpression apply(BooleanExpression context,
			SymbolicExpression expr, CIVLType civlType) {
		SymbolicOperator op = expr.operator();
		SymbolicType type = expr.type();

		switch (op) {
		case ARRAY_READ:
			return universe.arrayRead(
					apply(context, (SymbolicExpression) expr.argument(0),
							civlType), (NumericExpression) expr.argument(1));
		case ARRAY_WRITE:
			return universe.arrayWrite(
					apply(context, (SymbolicExpression) expr.argument(0),
							civlType),
					(NumericExpression) expr.argument(1),
					apply(context, (SymbolicExpression) expr.argument(2),
							civlType));
		case DENSE_ARRAY_WRITE: {
			@SuppressWarnings("unchecked")
			SymbolicSequence<? extends SymbolicExpression> oldElements = (SymbolicSequence<? extends SymbolicExpression>) expr
					.argument(1);
			int size = oldElements.size();
			SymbolicExpression[] newElements = new SymbolicExpression[size];

			for (int i = 0; i < size; i++)
				newElements[i] = apply(context, oldElements.get(i), civlType);
			return universe.denseArrayWrite(
					apply(context, (SymbolicExpression) expr.argument(0),
							civlType), Arrays.asList(newElements));
		}
		case LAMBDA:
			return universe.lambda(
					(SymbolicConstant) expr.argument(0),
					apply(context, (SymbolicExpression) expr.argument(1),
							civlType));
		case TUPLE_READ:
			return universe.tupleRead(
					apply(context, (SymbolicExpression) expr.argument(0),
							civlType), (IntObject) expr.argument(1));
		case ARRAY: {
			int n = expr.numArguments();
			SymbolicExpression[] newArgs = new SymbolicExpression[n];

			for (int i = 0; i < n; i++)
				newArgs[i] = apply(context,
						(SymbolicExpression) expr.argument(i), civlType);
			return universe.array(
					newType(((SymbolicArrayType) type).elementType()), newArgs);
		}
		case TUPLE: {
			if (type.equals(this.inputType))
				return this.rootOperation.apply(context, expr, civlType);

			int n = expr.numArguments();
			SymbolicExpression[] newArgs = new SymbolicExpression[n];

			for (int i = 0; i < n; i++)
				newArgs[i] = apply(context,
						(SymbolicExpression) expr.argument(i), civlType);
			return universe.tuple((SymbolicTupleType) newType(type), newArgs);
		}
		case ARRAY_LAMBDA:
			// TODO
		case COND:
			return universe.cond(
					(BooleanExpression) expr.argument(0),
					apply(context, (SymbolicExpression) expr.argument(1),
							civlType),
					apply(context, (SymbolicExpression) expr.argument(2),
							civlType));
		default:
			if (type.equals(inputType))
				return rootOperation.apply(context, expr, civlType);
			if (type.equals(outputType))
				return expr;

			SymbolicConstant f = uninterpretedFunctions.get(type);

			if (f == null) {
				f = universe.symbolicConstant(
						rootName,
						universe.functionType(Arrays.asList(type),
								this.newType(type)));
				uninterpretedFunctions.put(type, f);
			}
			return universe.apply(f, Arrays.asList(expr));
		}
	}
}
