/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Vector;

import edu.udel.cis.vsl.civl.err.CIVLException;
import edu.udel.cis.vsl.civl.err.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.SystemFunction;
import edu.udel.cis.vsl.civl.model.IF.expression.AddressOfExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression.BINARY_OPERATOR;
import edu.udel.cis.vsl.civl.model.IF.expression.BooleanLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.CastExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.DereferenceExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.DotExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.DynamicTypeOfExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.InitialValueExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.IntegerLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.RealLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.ResultExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SelfExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SizeofExpressionExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SizeofTypeExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.StringLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SubscriptExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.UnaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.UnaryExpression.UNARY_OPERATOR;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.AssertStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.AssignStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.AssumeStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.ChooseStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.MallocStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.NoopStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.ReturnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.WaitStatement;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLArrayType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLBundleType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLCompleteArrayType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLHeapType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPointerType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPrimitiveType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPrimitiveType.PrimitiveTypeKind;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLStructType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.type.StructField;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.model.common.expression.CommonAddressOfExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonBinaryExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonBooleanLiteralExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonCastExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonConditionalExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonDereferenceExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonDotExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonDynamicTypeOfExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonInitialValueExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonIntegerLiteralExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonRealLiteralExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonResultExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonSelfExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonSizeofExpressionExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonSizeofTypeExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonStringLiteralExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonSubscriptExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonUnaryExpression;
import edu.udel.cis.vsl.civl.model.common.expression.CommonVariableExpression;
import edu.udel.cis.vsl.civl.model.common.location.CommonLocation;
import edu.udel.cis.vsl.civl.model.common.statement.CommonAssertStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonAssignStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonAssumeStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonCallStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonChooseStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonMallocStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonNoopStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonReturnStatement;
import edu.udel.cis.vsl.civl.model.common.statement.CommonWaitStatement;
import edu.udel.cis.vsl.civl.model.common.type.CommonArrayType;
import edu.udel.cis.vsl.civl.model.common.type.CommonBundleType;
import edu.udel.cis.vsl.civl.model.common.type.CommonCompleteArrayType;
import edu.udel.cis.vsl.civl.model.common.type.CommonHeapType;
import edu.udel.cis.vsl.civl.model.common.type.CommonPointerType;
import edu.udel.cis.vsl.civl.model.common.type.CommonPrimitiveType;
import edu.udel.cis.vsl.civl.model.common.type.CommonStructField;
import edu.udel.cis.vsl.civl.model.common.type.CommonStructType;
import edu.udel.cis.vsl.civl.model.common.variable.CommonVariable;
import edu.udel.cis.vsl.civl.util.Singleton;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicUnionType;

/**
 * The factory to create all model components. Usually this is the only way
 * model components will be created.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class CommonModelFactory implements ModelFactory {

	/**
	 * Amount by which to increase the list of cached scope values and process
	 * values when a new value is requested that is outside of the current
	 * range.
	 */
	private final static int CACHE_INCREMENT = 10;

	private SymbolicUniverse universe;

	private CIVLSource systemSource = new SystemCIVLSource();

	/* Keep a unique number to identify locations. */
	private int locationID = 0;

	/* Keep a set of used identifiers for fly-weighting purposes. */
	private Map<String, Identifier> identifiers;

	private CIVLPrimitiveType voidType;

	private CIVLPrimitiveType integerType;

	private CIVLPrimitiveType booleanType;

	private CIVLPrimitiveType realType;

	private CIVLPrimitiveType scopeType;

	private CIVLPrimitiveType processType;

	private CIVLPrimitiveType dynamicType;

	private CIVLPrimitiveType stringType;

	private SymbolicTupleType scopeSymbolicType;

	private SymbolicTupleType processSymbolicType;

	private SymbolicTupleType dynamicSymbolicType;

	private SymbolicTupleType pointerSymbolicType;

	private SymbolicArrayType stringSymbolicType;

	/* Keep a unique number to identify scopes. */
	private int scopeID = 0;

	private int chooseID = 0;

	// private Scope systemScope;

	private IntObject zeroObj;

	private ArrayList<SymbolicExpression> processValues = new ArrayList<SymbolicExpression>();

	private ArrayList<SymbolicExpression> scopeValues = new ArrayList<SymbolicExpression>();

	private SymbolicExpression undefinedProcessValue;

	private SymbolicExpression undefinedScopeValue;

	/** A list of nulls of length CACHE_INCREMENT */
	private List<SymbolicExpression> nullList = new LinkedList<SymbolicExpression>();

	/**
	 * The factory to create all model components. Usually this is the only way
	 * model components will be created.
	 */
	public CommonModelFactory(SymbolicUniverse universe) {
		Iterable<SymbolicType> intTypeSingleton = new Singleton<SymbolicType>(
				universe.integerType());
		LinkedList<SymbolicType> pointerComponents = new LinkedList<SymbolicType>();

		this.universe = universe;
		this.voidType = primitiveType(PrimitiveTypeKind.VOID, null);
		this.integerType = primitiveType(PrimitiveTypeKind.INT,
				universe.integerType());
		this.booleanType = primitiveType(PrimitiveTypeKind.BOOL,
				universe.booleanType());
		this.realType = primitiveType(PrimitiveTypeKind.REAL,
				universe.realType());

		this.identifiers = new HashMap<String, Identifier>();
		scopeSymbolicType = (SymbolicTupleType) universe.canonic(universe
				.tupleType(universe.stringObject("scope"), intTypeSingleton));
		scopeType = primitiveType(PrimitiveTypeKind.SCOPE, scopeSymbolicType);
		processSymbolicType = (SymbolicTupleType) universe.canonic(universe
				.tupleType(universe.stringObject("process"), intTypeSingleton));
		processType = primitiveType(PrimitiveTypeKind.PROCESS,
				processSymbolicType);
		dynamicSymbolicType = (SymbolicTupleType) universe.canonic(universe
				.tupleType(universe.stringObject("dynamicType"),
						intTypeSingleton));
		dynamicType = primitiveType(PrimitiveTypeKind.DYNAMIC,
				dynamicSymbolicType);
		pointerComponents.add(scopeType.getDynamicType(universe));
		pointerComponents.add(universe.integerType());
		pointerComponents.add(universe.referenceType());
		pointerSymbolicType = (SymbolicTupleType) universe
				.canonic(universe.tupleType(universe.stringObject("pointer"),
						pointerComponents));
		stringSymbolicType = (SymbolicArrayType) universe.canonic(universe
				.arrayType(universe.characterType()));
		stringType = primitiveType(PrimitiveTypeKind.STRING, stringSymbolicType);
		zeroObj = (IntObject) universe.canonic(universe.intObject(0));
		for (int i = 0; i < CACHE_INCREMENT; i++)
			nullList.add(null);
		undefinedProcessValue = universe.canonic(universe.tuple(
				processSymbolicType,
				new Singleton<SymbolicExpression>(universe.integer(-1))));
		undefinedScopeValue = universe.canonic(universe.tuple(
				scopeSymbolicType,
				new Singleton<SymbolicExpression>(universe.integer(-1))));
	}

	private NumericExpression sizeofExpression(PrimitiveTypeKind kind) {
		NumericExpression result = (NumericExpression) universe
				.symbolicConstant(universe.stringObject("SIZEOF_" + kind),
						universe.integerType());

		result = (NumericExpression) universe.canonic(result);
		return result;
	}

	private CIVLPrimitiveType primitiveType(PrimitiveTypeKind kind,
			SymbolicType dynamicType) {
		CIVLPrimitiveType result;
		NumericExpression size = null;
		BooleanExpression fact = null;

		if (dynamicType != null)
			dynamicType = (SymbolicType) universe.canonic(dynamicType);
		if (kind != PrimitiveTypeKind.VOID)
			size = sizeofExpression(kind);
		if (size == null)
			fact = universe.trueExpression();
		else
			fact = universe.lessThan(universe.zeroInt(), size);
		fact = (BooleanExpression) universe.canonic(fact);
		result = new CommonPrimitiveType(kind, dynamicType, size, fact);
		return result;
	}

	@Override
	public CIVLSource systemSource() {
		return systemSource;
	}

	/**
	 * Create a new model.
	 * 
	 * @param system
	 *            The designated outermost function, called "System."
	 */
	@Override
	public Model model(CIVLSource civlSource, CIVLFunction system) {
		return new CommonModel(civlSource, this, system);
	}

	/**
	 * Create a new scope.
	 * 
	 * @param parent
	 *            The containing scope of this scope. Only null for the
	 *            outermost scope of the designated "System" function.
	 * @param variables
	 *            The set of variables in this scope.
	 * @param function
	 *            The function containing this scope.
	 * @return A new scope
	 */
	@Override
	public Scope scope(CIVLSource source, Scope parent,
			Set<Variable> variables, CIVLFunction function) {
		Scope newScope = new CommonScope(source, parent, variables, scopeID++);
		if (parent != null) {
			parent.addChild(newScope);
		}
		newScope.setFunction(function);
		return newScope;
	}

	/**
	 * Get an identifier with the given name.
	 * 
	 * @param name
	 *            The name of this identifier.
	 */
	@Override
	public Identifier identifier(CIVLSource source, String name) {
		Identifier result = identifiers.get(name);

		if (result == null) {
			StringObject stringObject = (StringObject) universe
					.canonic(universe.stringObject(name));

			result = new CommonIdentifier(source, stringObject);
			identifiers.put(name, result);
		}
		return result;
	}

	/**
	 * Create a new variable.
	 * 
	 * @param type
	 *            The type of this variable.
	 * @param name
	 *            The name of this variable.
	 * @param vid
	 *            The index of this variable in its scope.
	 */
	@Override
	public Variable variable(CIVLSource source, CIVLType type, Identifier name,
			int vid) {
		return new CommonVariable(source, type, name, vid);
	}

	/**
	 * Create a new function.
	 * 
	 * @param name
	 *            The name of this function.
	 * @param parameters
	 *            The list of parameters.
	 * @param returnType
	 *            The return type of this function.
	 * @param containingScope
	 *            The scope containing this function.
	 * @param startLocation
	 *            The first location in the function.
	 * @return The new function.
	 */
	@Override
	public CIVLFunction function(CIVLSource source, Identifier name,
			Vector<Variable> parameters, CIVLType returnType,
			Scope containingScope, Location startLocation) {
		for (Variable v : parameters) {
			if (v.type() instanceof CIVLArrayType) {
				throw new CIVLInternalException("Parameter of array type.", v);
			}
		}
		return new CommonFunction(source, name, parameters, returnType,
				containingScope, startLocation, this);
	}

	/**
	 * Create a record of a system function.
	 * 
	 * @param name
	 *            The name of this function.
	 */
	@Override
	public SystemFunction systemFunction(CIVLSource source, Identifier name,
			Vector<Variable> parameters, CIVLType returnType,
			Scope containingScope, String libraryName) {
		return new CommonSystemFunction(source, name, parameters, returnType,
				containingScope, (Location) null, this, libraryName);
	}

	/**
	 * Create a new location.
	 * 
	 * @param scope
	 *            The scope containing this location.
	 * @return The new location.
	 */
	@Override
	public Location location(CIVLSource source, Scope scope) {
		return new CommonLocation(source, scope, locationID++);
	}

	/* *********************************************************************
	 * Types
	 * *********************************************************************
	 */

	/**
	 * Get the integer primitive type.
	 * 
	 * @return The integer primitive type.
	 */
	@Override
	public CIVLPrimitiveType integerType() {
		return integerType;
	}

	/**
	 * Get the real primitive type.
	 * 
	 * @return The real primitive type.
	 */
	@Override
	public CIVLPrimitiveType realType() {
		return realType;
	}

	/**
	 * Get the boolean primitive type.
	 * 
	 * @return The boolean primitive type.
	 */
	@Override
	public CIVLPrimitiveType booleanType() {
		return booleanType;
	}

	/**
	 * Get the string primitive type.
	 * 
	 * @return The string primitive type.
	 */
	@Override
	public CIVLPrimitiveType stringType() {
		return stringType;
	}

	/**
	 * Get the scope primitive type.
	 * 
	 * @return The scope primitive type.
	 */
	@Override
	public CIVLPrimitiveType scopeType() {
		return scopeType;
	}

	/**
	 * Get the process type.
	 * 
	 * @return The process type.
	 */
	@Override
	public CIVLPrimitiveType processType() {
		return processType;
	}

	@Override
	public CIVLPrimitiveType dynamicType() {
		return dynamicType;
	}

	/**
	 * Get a new array type.
	 * 
	 * @param baseType
	 *            The type of each element in the array.
	 * @return A new array type with the given base type.
	 */
	@Override
	public CIVLArrayType incompleteArrayType(CIVLType baseType) {
		return new CommonArrayType(baseType);
	}

	@Override
	public CIVLCompleteArrayType completeArrayType(CIVLType elementType,
			Expression extent) {
		return new CommonCompleteArrayType(elementType, extent);
	}

	/**
	 * Get a new pointer type.
	 * 
	 * @param baseType
	 *            The type of element pointed to by the pointer.
	 * @return A new pointer type with the given base type.
	 */
	@Override
	public CIVLPointerType pointerType(CIVLType baseType) {
		return new CommonPointerType(baseType, pointerSymbolicType);
	}

	@Override
	public CIVLStructType structType(Identifier name) {
		return new CommonStructType(name);
	}

	/**
	 * Get a struct field.
	 * 
	 * @param name
	 *            Identifier for the name of this struct member.
	 * @param type
	 *            The type of this struct member.
	 * @return A struct field with the given name and type.
	 */
	@Override
	public StructField structField(Identifier name, CIVLType type) {
		return new CommonStructField(name, type);
	}

	/* *********************************************************************
	 * Expressions
	 * *********************************************************************
	 */

	/**
	 * A unary expression. One of {-,!}.
	 * 
	 * @param operator
	 *            The unary operator.
	 * @param operand
	 *            The expression to which the operator is applied.
	 * @return The unary expression.
	 */
	@Override
	public UnaryExpression unaryExpression(CIVLSource source,
			UNARY_OPERATOR operator, Expression operand) {
		UnaryExpression result = new CommonUnaryExpression(source, operator,
				operand);

		result.setExpressionScope(operand.expressionScope());
		switch (operator) {
		case NEGATIVE:
			result = new CommonUnaryExpression(source, operator, operand);
			((CommonUnaryExpression) result).setExpressionType(operand
					.getExpressionType());
			break;
		case NOT:
			if (operand.getExpressionType().equals(booleanType)) {
				result = new CommonUnaryExpression(source, operator, operand);
			} else {
				// TODO: This often won't work. Need to do conversion for e.g.
				// numeric types
				Expression castOperand = castExpression(source, booleanType,
						operand);
				result = new CommonUnaryExpression(source, operator,
						castOperand);
			}
			((CommonUnaryExpression) result).setExpressionType(booleanType);
			break;
		default:
			throw new CIVLInternalException("Unknown unary operator: "
					+ operator, source);

		}
		return result;
	}

	/**
	 * A binary expression. One of {+,-,*,\,<,<=,==,!=,&&,||,%}
	 * 
	 * @param operator
	 *            The binary operator.
	 * @param left
	 *            The left operand.
	 * @param right
	 *            The right operand.
	 * @return The binary expression.
	 */
	@Override
	public BinaryExpression binaryExpression(CIVLSource source,
			BINARY_OPERATOR operator, Expression left, Expression right) {
		BinaryExpression result = new CommonBinaryExpression(source, operator,
				left, right);

		result.setExpressionScope(join(left.expressionScope(),
				right.expressionScope()));
		switch (operator) {
		case AND:
		case EQUAL:
		case LESS_THAN:
		case LESS_THAN_EQUAL:
		case NOT_EQUAL:
		case OR:
			((CommonBinaryExpression) result).setExpressionType(booleanType);
			break;
		case PLUS:
		case TIMES:
		case DIVIDE:
		case MINUS:
		case MODULO:
		default:
			CIVLType leftType = left.getExpressionType();
			CIVLType rightType = right.getExpressionType();

			// Types should be the same unless we're doing pointer arithmetic.
			if (leftType.equals(rightType)) {
				((CommonBinaryExpression) result).setExpressionType(leftType);
			} else if (leftType instanceof CIVLPointerType
					&& rightType instanceof CIVLPrimitiveType) {
				assert ((CIVLPrimitiveType) rightType).primitiveTypeKind() == PrimitiveTypeKind.INT;
				((CommonBinaryExpression) result).setExpressionType(leftType);
			} else if (leftType instanceof CIVLPointerType
					&& rightType instanceof CIVLPrimitiveType) {
				assert ((CIVLPrimitiveType) rightType).primitiveTypeKind() == PrimitiveTypeKind.INT;
				((CommonBinaryExpression) result).setExpressionType(leftType);
			} else
				throw new CIVLException("Incompatible types to +", source);
			break;
		}
		return result;
	}

	/**
	 * A cast of an expression to another type.
	 * 
	 * @param type
	 *            The type to which the expression is cast.
	 * @param expresssion
	 *            The expression being cast to a new type.
	 */
	@Override
	public CastExpression castExpression(CIVLSource source, CIVLType type,
			Expression expression) {
		CastExpression result = new CommonCastExpression(source, type,
				expression);

		result.setExpressionScope(expression.expressionScope());
		((CommonCastExpression) result).setExpressionType(type);
		return result;
	}

	@Override
	public SizeofTypeExpression sizeofTypeExpression(CIVLSource source,
			CIVLType type) {
		CommonSizeofTypeExpression result = new CommonSizeofTypeExpression(
				source, type);

		// result.setExpressionScope() don't know
		result.setExpressionType(integerType);
		return result;
	}

	@Override
	public DynamicTypeOfExpression dynamicTypeOfExpression(CIVLSource source,
			CIVLType type) {
		CommonDynamicTypeOfExpression result = new CommonDynamicTypeOfExpression(
				source, type);

		// result.setExpressionScope(expressionScope)
		result.setExpressionType(dynamicType);
		return result;
	}

	@Override
	public InitialValueExpression initialValueExpression(CIVLSource source,
			Variable variable) {
		CommonInitialValueExpression result = new CommonInitialValueExpression(
				source, variable);

		// result.setExpressionScope(expressionScope)
		result.setExpressionType(variable.type());
		return result;
	}

	/**
	 * The ternary conditional expression ("?" in C).
	 * 
	 * @param condition
	 *            The condition being evaluated in this conditional.
	 * @param trueBranch
	 *            The expression returned if the condition evaluates to true.
	 * @param falseBranch
	 *            The expression returned if the condition evaluates to false.
	 * @return The conditional expression.
	 */
	@Override
	public ConditionalExpression conditionalExpression(CIVLSource source,
			Expression condition, Expression trueBranch, Expression falseBranch) {
		ConditionalExpression result = new CommonConditionalExpression(source,
				condition, trueBranch, falseBranch);

		result.setExpressionScope(join(
				condition.expressionScope(),
				join(trueBranch.expressionScope(),
						falseBranch.expressionScope())));
		assert trueBranch.getExpressionType().equals(
				falseBranch.getExpressionType());
		((CommonConditionalExpression) result).setExpressionType(trueBranch
				.getExpressionType());
		return result;
	}

	/**
	 * A dot expression is a reference to a struct field.
	 * 
	 * @param struct
	 *            The struct being referenced.
	 * @param field
	 *            The field.
	 * @return The dot expression.
	 */
	@Override
	public DotExpression dotExpression(CIVLSource source, Expression struct,
			int fieldIndex) {
		CommonDotExpression result = new CommonDotExpression(source, struct,
				fieldIndex);
		CIVLType structType = struct.getExpressionType();

		result.setExpressionScope(struct.expressionScope());
		assert structType instanceof CIVLStructType;
		result.setExpressionType(((CIVLStructType) structType).getField(
				fieldIndex).type());
		return result;
	}

	/**
	 * A boolean literal expression.
	 * 
	 * @param value
	 *            True or false.
	 * @return The boolean literal expression.
	 */
	@Override
	public BooleanLiteralExpression booleanLiteralExpression(CIVLSource source,
			boolean value) {
		CommonBooleanLiteralExpression result;

		result = new CommonBooleanLiteralExpression(source, value);
		result.setExpressionType(booleanType);
		return result;
	}

	/**
	 * An integer literal expression.
	 * 
	 * @param value
	 *            The (arbitrary precision) integer value.
	 * @return The integer literal expression.
	 */
	@Override
	public IntegerLiteralExpression integerLiteralExpression(CIVLSource source,
			BigInteger value) {
		IntegerLiteralExpression result = new CommonIntegerLiteralExpression(
				source, value);

		((CommonIntegerLiteralExpression) result)
				.setExpressionType(integerType);
		return result;
	}

	/**
	 * A real literal expression.
	 * 
	 * @param value
	 *            The (arbitrary precision) real value.
	 * @return The real literal expression.
	 */
	@Override
	public RealLiteralExpression realLiteralExpression(CIVLSource source,
			BigDecimal value) {
		RealLiteralExpression result = new CommonRealLiteralExpression(source,
				value);

		((CommonRealLiteralExpression) result).setExpressionType(realType);
		return result;
	}

	/**
	 * This expression is only used in an ensures clause of a function contract
	 * to refer to the returned value.
	 * 
	 * @return A result expression.
	 */
	@Override
	public ResultExpression resultExpression(CIVLSource source) {
		return new CommonResultExpression(source);
	}

	/**
	 * A string literal expression.
	 * 
	 * @param value
	 *            The string.
	 * @return The string literal expression.
	 */
	@Override
	public StringLiteralExpression stringLiteralExpression(CIVLSource source,
			String value) {
		StringLiteralExpression result = new CommonStringLiteralExpression(
				source, value);

		((CommonStringLiteralExpression) result).setExpressionType(stringType);
		return result;
	}

	/**
	 * An expression for an array index operation. e.g. a[i]
	 * 
	 * @param array
	 *            An expression evaluating to an array.
	 * @param index
	 *            An expression evaluating to an integer.
	 * @return The array index expression.
	 */
	@Override
	public SubscriptExpression subscriptExpression(CIVLSource source,
			LHSExpression array, Expression index) {
		SubscriptExpression result = new CommonSubscriptExpression(source,
				array, index);
		CIVLType arrayType = array.getExpressionType();

		result.setExpressionScope(join(array.expressionScope(),
				index.expressionScope()));
		if (arrayType instanceof CIVLArrayType) {
			((CommonSubscriptExpression) result)
					.setExpressionType(((CIVLArrayType) arrayType)
							.elementType());
		} else if (arrayType instanceof CIVLPointerType) {
			((CommonSubscriptExpression) result)
					.setExpressionType(((CIVLPointerType) arrayType).baseType());
		} else {
			throw new RuntimeException(
					"Unable to set expression type for expression: " + result);
		}
		return result;
	}

	/**
	 * A self expression. Used to referenced the current process.
	 * 
	 * @return A new self expression.
	 */
	@Override
	public SelfExpression selfExpression(CIVLSource source) {
		SelfExpression result = new CommonSelfExpression(source);

		((CommonSelfExpression) result).setExpressionType(processType);
		return result;
	}

	/**
	 * A variable expression.
	 * 
	 * @param variable
	 *            The variable being referenced.
	 * @return The variable expression.
	 */
	@Override
	public VariableExpression variableExpression(CIVLSource source,
			Variable variable) {
		VariableExpression result = new CommonVariableExpression(source,
				variable);

		// Don't need to worry about the expression scope of constants.
		if (!variable.isConst()) {
			result.setExpressionScope(variable.scope());
		}
		((CommonVariableExpression) result).setExpressionType(variable.type());
		return result;
	}

	/* *********************************************************************
	 * Statements
	 * *********************************************************************
	 */

	/**
	 * An assert statement.
	 * 
	 * @param source
	 *            The source location for this statement.
	 * @param expression
	 *            The expression being asserted.
	 * @return A new assert statement.
	 */
	@Override
	public AssertStatement assertStatement(CIVLSource civlSource,
			Location source, Expression expression) {
		AssertStatement result = new CommonAssertStatement(civlSource, source,
				expression);

		((CommonExpression) result.guard()).setExpressionType(booleanType);
		result.setStatementScope(expression.expressionScope());
		return result;
	}

	/**
	 * An assignment statement.
	 * 
	 * @param source
	 *            The source location for this statement.
	 * @param lhs
	 *            The left hand side of the assignment.
	 * @param rhs
	 *            The right hand side of the assignment.
	 * @return A new assignment statement.
	 */
	@Override
	public AssignStatement assignStatement(CIVLSource civlSource,
			Location source, LHSExpression lhs, Expression rhs) {
		AssignStatement result = new CommonAssignStatement(civlSource, source,
				lhs, rhs);

		result.setStatementScope(join(lhs.expressionScope(),
				rhs.expressionScope()));
		((CommonExpression) result.guard()).setExpressionType(booleanType);
		return result;
	}

	/**
	 * An assume statement.
	 * 
	 * @param source
	 *            The source location for this statement.
	 * @param expression
	 *            The expression being added to the path condition.
	 * @return A new assume statement.
	 */
	@Override
	public AssumeStatement assumeStatement(CIVLSource civlSource,
			Location source, Expression expression) {
		AssumeStatement result = new CommonAssumeStatement(civlSource, source,
				expression);

		result.setStatementScope(expression.expressionScope());
		((CommonExpression) result.guard()).setExpressionType(booleanType);
		return result;
	}

	/**
	 * A function call.
	 * 
	 * @param source
	 *            The source location for this call statement.
	 * @param function
	 *            The function.
	 * @param arguments
	 *            The arguments to the function.
	 * @return A new call statement.
	 */
	@Override
	public CallOrSpawnStatement callOrSpawnStatement(CIVLSource civlSource,
			Location source, boolean isCall, CIVLFunction function,
			Vector<Expression> arguments) {
		CallOrSpawnStatement result = new CommonCallStatement(civlSource,
				source, isCall, function, arguments);
		Scope statementScope = null;

		((CommonExpression) result.guard()).setExpressionType(booleanType);
		for (Expression arg : arguments) {
			statementScope = join(statementScope, arg.expressionScope());
		}
		result.setStatementScope(statementScope);
		return result;
	}

	/**
	 * A choose statement is of the form x = choose(n);
	 * 
	 * When a choose statement is executed, the left hand side will be assigned
	 * a new symbolic constant. A bound on the values of that symbolic constant
	 * will be added to the path condition.
	 * 
	 * @param source
	 *            The source location for this statement.
	 * @param lhs
	 *            The left hand side of the choose statement.
	 * @param argument
	 *            The argument to choose().
	 * @return A new choose statement.
	 */
	@Override
	public ChooseStatement chooseStatement(CIVLSource civlSource,
			Location source, LHSExpression lhs, Expression argument) {
		ChooseStatement result = new CommonChooseStatement(civlSource, source,
				lhs, argument, chooseID++);

		result.setStatementScope(join(lhs.expressionScope(),
				argument.expressionScope()));
		((CommonExpression) result.guard()).setExpressionType(booleanType);
		return result;
	}

	/**
	 * A join statement. Used to wait for a process to complete.
	 * 
	 * @param source
	 *            The source location for this join statement.
	 * @param process
	 *            An expression evaluating to a process.
	 * @return A new join statement.
	 */
	@Override
	public WaitStatement joinStatement(CIVLSource civlSource, Location source,
			Expression process) {
		WaitStatement result = new CommonWaitStatement(civlSource, source,
				process);

		result.setStatementScope(process.expressionScope());
		((CommonExpression) result.guard()).setExpressionType(booleanType);
		return result;
	}

	/**
	 * A noop statement.
	 * 
	 * @param source
	 *            The source location for this noop statement.
	 * @return A new noop statement.
	 */
	@Override
	public NoopStatement noopStatement(CIVLSource civlSource, Location source) {
		NoopStatement result = new CommonNoopStatement(civlSource, source);

		((CommonExpression) result.guard()).setExpressionType(booleanType);
		return result;
	}

	/**
	 * A return statement.
	 * 
	 * @param source
	 *            The source location for this return statement.
	 * @param expression
	 *            The expression being returned. Null if non-existent.
	 * @return A new return statement.
	 */
	@Override
	public ReturnStatement returnStatement(CIVLSource civlSource,
			Location source, Expression expression) {
		ReturnStatement result = new CommonReturnStatement(civlSource, source,
				expression);

		if (expression != null) {
			result.setStatementScope(expression.expressionScope());
		}
		((CommonExpression) result.guard()).setExpressionType(booleanType);
		return result;
	}

	/**
	 * @param s0
	 *            A scope. May be null.
	 * @param s1
	 *            A scope. May be null.
	 * @return The scope that is the join, or least common ancestor in the scope
	 *         tree, of s0 and s1. Null if both are null. If exactly one of s0
	 *         and s1 are null, returns the non-null scope.
	 */
	private Scope join(Scope s0, Scope s1) {
		Vector<Scope> s0Ancestors = new Vector<Scope>();
		Scope s0Ancestor = s0;
		Scope s1Ancestor = s1;

		if (s0 == null) {
			return s1;
		} else if (s1 == null) {
			return s0;
		}
		s0Ancestors.add(s0Ancestor);
		while (s0Ancestor.parent() != null) {
			s0Ancestor = s0Ancestor.parent();
			s0Ancestors.add(s0Ancestor);
		}
		while (true) {
			if (s0Ancestors.contains(s1Ancestor)) {
				return s1Ancestor;
			}
			s1Ancestor = s1Ancestor.parent();
		}
	}

	/**
	 * Gets a Java conrete int from a symbolic expression or throws exception.
	 * 
	 * @param expression
	 *            a numeric expression expected to hold concrete int value
	 * @return the concrete int
	 * @throws CIVLInternalException
	 *             if a concrete integer value cannot be extracted
	 */
	private int extractInt(CIVLSource source, NumericExpression expression) {
		IntegerNumber result = (IntegerNumber) universe
				.extractNumber(expression);

		if (result == null)
			throw new CIVLInternalException(
					"Unable to extract concrete int from " + expression, source);
		return result.intValue();
	}

	/**
	 * Gets a concrete Java int from the field of a symbolic expression of tuple
	 * type or throws exception.
	 * 
	 * @param tuple
	 *            symbolic expression of tuple type
	 * @param fieldIndex
	 *            index of a field in that tuple
	 * @return the concrete int value of that field
	 * @throws CIVLInternalException
	 *             if a concrete integer value cannot be extracted
	 */
	private int extractIntField(CIVLSource source, SymbolicExpression tuple,
			IntObject fieldIndex) {
		NumericExpression field = (NumericExpression) universe.tupleRead(tuple,
				fieldIndex);

		return extractInt(source, field);
	}

	@Override
	public DereferenceExpression dereferenceExpression(CIVLSource source,
			Expression pointer) {
		CIVLPointerType pointerType = (CIVLPointerType) pointer
				.getExpressionType();
		DereferenceExpression result = new CommonDereferenceExpression(source,
				pointer);

		result.setExpressionScope(null); // indicates unknown scope
		((CommonExpression) result).setExpressionType(pointerType.baseType());
		return result;
	}

	@Override
	public AddressOfExpression addressOfExpression(CIVLSource source,
			LHSExpression operand) {
		AddressOfExpression result = new CommonAddressOfExpression(source,
				operand);

		result.setExpressionScope(operand.expressionScope());
		((CommonExpression) result).setExpressionType(this.pointerType(operand
				.getExpressionType()));
		return result;
	}

	@Override
	public SymbolicUniverse universe() {
		return universe;
	}

	@Override
	public SymbolicTupleType pointerSymbolicType() {
		return pointerSymbolicType;
	}

	@Override
	public SymbolicTupleType processSymbolicType() {
		return processSymbolicType;
	}

	@Override
	public SymbolicTupleType dynamicSymbolicType() {
		return dynamicSymbolicType;
	}

	@Override
	public SymbolicTupleType scopeSymbolicType() {
		return scopeSymbolicType;
	}

	@Override
	public SymbolicArrayType stringSymbolicType() {
		return stringSymbolicType;
	}

	@Override
	public CIVLPrimitiveType voidType() {
		return voidType;
	}

	@Override
	public SymbolicExpression processValue(int pid) {
		SymbolicExpression result;

		if (pid < 0)
			return undefinedProcessValue;
		while (pid >= processValues.size())
			processValues.addAll(nullList);
		result = processValues.get(pid);
		if (result == null) {
			result = universe.canonic(universe.tuple(processSymbolicType,
					new Singleton<SymbolicExpression>(universe.integer(pid))));
			processValues.set(pid, result);
		}
		return result;
	}

	@Override
	public int getProcessId(CIVLSource source, SymbolicExpression processValue) {
		return extractIntField(source, processValue, zeroObj);
	}

	@Override
	public SymbolicExpression scopeValue(int sid) {
		SymbolicExpression result;

		if (sid < 0)
			return undefinedScopeValue;
		while (sid >= scopeValues.size())
			scopeValues.addAll(nullList);
		result = scopeValues.get(sid);
		if (result == null) {
			result = universe.canonic(universe.tuple(scopeSymbolicType,
					new Singleton<SymbolicExpression>(universe.integer(sid))));
			scopeValues.set(sid, result);
		}
		return result;
	}

	@Override
	public int getScopeId(CIVLSource source, SymbolicExpression scopeValue) {
		return extractIntField(source, scopeValue, zeroObj);
	}

	private SymbolicExpression undefinedValue(SymbolicType type) {
		SymbolicExpression result = universe.symbolicConstant(
				universe.stringObject("UNDEFINED"), type);

		result = universe.canonic(result);
		return result;
	}

	private SymbolicExpression computeInitialHeapValue(
			SymbolicTupleType heapDynamicType) {
		LinkedList<SymbolicExpression> fields = new LinkedList<SymbolicExpression>();
		SymbolicExpression result;

		for (SymbolicType fieldType : heapDynamicType.sequence()) {
			SymbolicArrayType arrayType = (SymbolicArrayType) fieldType;
			SymbolicType objectType = arrayType.elementType();
			SymbolicExpression emptyArray = universe.emptyArray(objectType);

			fields.add(emptyArray);
		}
		result = universe.tuple(heapDynamicType, fields);
		result = universe.canonic(result);
		return result;
	}

	private SymbolicTupleType computeDynamicHeapType(
			Iterable<MallocStatement> mallocStatements) {
		LinkedList<SymbolicType> fieldTypes = new LinkedList<SymbolicType>();
		SymbolicTupleType result;

		for (MallocStatement statement : mallocStatements) {
			SymbolicType fieldType = universe.arrayType(statement
					.getDynamicObjectType());

			fieldTypes.add(fieldType);
		}
		result = universe.tupleType(universe.stringObject("$heap"), fieldTypes);
		result = (SymbolicTupleType) universe.canonic(result);
		return result;
	}

	@Override
	public MallocStatement mallocStatement(CIVLSource civlSource,
			Location source, LHSExpression lhs, CIVLType staticElementType,
			Expression heapPointerExpression, Expression sizeExpression,
			int mallocId) {
		SymbolicType dynamicElementType = staticElementType
				.getDynamicType(universe);
		SymbolicArrayType dynamicObjectType = (SymbolicArrayType) universe
				.canonic(universe.arrayType(dynamicElementType));
		SymbolicExpression undefinedObject = undefinedValue(dynamicObjectType);
		MallocStatement result = new CommonMallocStatement(civlSource, source,
				mallocId, heapPointerExpression, staticElementType,
				dynamicElementType, dynamicObjectType, sizeExpression,
				undefinedObject, lhs);

		return result;
	}

	@Override
	public CIVLHeapType heapType(String name) {
		return new CommonHeapType(name);
	}

	@Override
	public void completeHeapType(CIVLHeapType heapType,
			Collection<MallocStatement> mallocs) {
		SymbolicTupleType dynamicType = computeDynamicHeapType(mallocs);
		SymbolicExpression initialValue = computeInitialHeapValue(dynamicType);
		SymbolicExpression undefinedValue = universe.symbolicConstant(
				universe.stringObject("UNDEFINED"), dynamicType);

		undefinedValue = universe.canonic(undefinedValue);
		heapType.complete(mallocs, dynamicType, initialValue, undefinedValue);
	}

	@Override
	public SizeofExpressionExpression sizeofExpressionExpression(
			CIVLSource source, Expression argument) {
		CommonSizeofExpressionExpression result = new CommonSizeofExpressionExpression(
				source, argument);

		result.setExpressionScope(argument.expressionScope());
		result.setExpressionType(integerType);
		return result;
	}

	@Override
	public CIVLBundleType newBundleType() {
		return new CommonBundleType();
	}

	@Override
	public void complete(CIVLBundleType bundleType,
			Collection<SymbolicType> elementTypes) {
		LinkedList<SymbolicType> arrayTypes = new LinkedList<SymbolicType>();
		SymbolicUnionType dynamicType;

		for (SymbolicType type : elementTypes)
			arrayTypes.add(universe.arrayType(type));
		dynamicType = universe.unionType(universe.stringObject("$bundle"),
				arrayTypes);
		dynamicType = (SymbolicUnionType) universe.canonic(dynamicType);
		bundleType.complete(elementTypes, dynamicType);
	}

}
