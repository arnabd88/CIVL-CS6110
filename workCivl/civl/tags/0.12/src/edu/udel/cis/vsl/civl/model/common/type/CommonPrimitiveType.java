package edu.udel.cis.vsl.civl.model.common.type;

import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPrimitiveType;
import edu.udel.cis.vsl.civl.util.IF.Singleton;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

/**
 * Implementation of {@link CIVLPrimitiveType}.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class CommonPrimitiveType extends CommonType implements
		CIVLPrimitiveType {

	private PrimitiveTypeKind kind;

	private NumericExpression sizeofExpression;

	private BooleanExpression facts;

	/**
	 * Constructs new primitive type instance with given parameters
	 * 
	 * @param kind
	 *            the kind of primitive type; may not be null
	 * @param symbolicType
	 *            the symbolic type corresponding to this primitive type; may be
	 *            null here but then must be set later
	 * @param sizeofExpression
	 *            the value that will be returned when evaluating "sizeof" this
	 *            type; null indicates this type should never occur in a sizeof
	 *            expression and if it does an exception will be thrown
	 * @param facts
	 *            boolean predicates concerned with this type which must hold,
	 *            e.g., sizeof(t)>0 or sizeof(t)=1
	 * 
	 */
	public CommonPrimitiveType(PrimitiveTypeKind kind,
			SymbolicType symbolicType, NumericExpression sizeofExpression,
			BooleanExpression facts) {
		super();
		this.dynamicType = symbolicType;
		this.kind = kind;
		this.sizeofExpression = sizeofExpression;
		this.facts = facts;
	}

	/**
	 * @return The actual primitive type (int, bool, real, or string).
	 */
	public PrimitiveTypeKind primitiveTypeKind() {
		return kind;
	}

	/**
	 * @param The
	 *            actual primitive type (int, bool, real, or string).
	 */
	public void setPrimitiveType(PrimitiveTypeKind primitiveType) {
		this.kind = primitiveType;
	}

	@Override
	public String toString() {
		switch (kind) {
		case INT:
			return "int";
		case BOOL:
			return "$bool";
		case REAL:
			return "$real";
		case SCOPE:
			return "$scope";
		case PROCESS:
			return "$proc";
		case DYNAMIC:
			return "$dynamicType";
		case VOID:
			return "void";
		case CHAR:
			return "char";
		default:
			throw new CIVLInternalException("Unknown primitive type kind: "
					+ kind, (CIVLSource) null);
		}
	}

	@Override
	public boolean isNumericType() {
		return kind == PrimitiveTypeKind.INT || kind == PrimitiveTypeKind.REAL;
	}

	@Override
	public boolean isIntegerType() {
		return kind == PrimitiveTypeKind.INT;
	}

	@Override
	public boolean isRealType() {
		return kind == PrimitiveTypeKind.REAL;
	}

	@Override
	public boolean isProcessType() {
		return kind == PrimitiveTypeKind.PROCESS;
	}

	@Override
	public boolean isScopeType() {
		return kind == PrimitiveTypeKind.SCOPE;
	}

	@Override
	public boolean isBoolType() {
		return kind == PrimitiveTypeKind.BOOL;
	}

	@Override
	public boolean hasState() {
		return false;
	}

	@Override
	public boolean isVoidType() {
		return kind == PrimitiveTypeKind.VOID;
	}

	@Override
	public NumericExpression getSizeof() {
		return sizeofExpression;
	}

	@Override
	public BooleanExpression getFacts() {
		return facts;
	}

	public void setDynamicType(SymbolicType dynamicType) {
		this.dynamicType = dynamicType;
	}

	@Override
	public SymbolicType getDynamicType(SymbolicUniverse universe) {
		if (dynamicType == null && kind != PrimitiveTypeKind.VOID)
			throw new CIVLInternalException(
					"no dynamic type specified for primitive type " + kind,
					(CIVLSource) null);
		return dynamicType;
	}

	@Override
	public boolean isCharType() {
		return kind == PrimitiveTypeKind.CHAR;
	}

	@Override
	public SymbolicExpression initialValue(SymbolicUniverse universe) {
		switch (this.kind) {
		case BOOL:
			return universe.bool(false);
		case DYNAMIC:
			return null;
		case INT:
			return universe.integer(0);
		case PROCESS:
			return universe.canonic(universe.tuple(
					(SymbolicTupleType) this.dynamicType,
					new Singleton<SymbolicExpression>(universe.integer(-2))));
		case REAL:
			return universe.rational(0);
		case SCOPE:
			return universe.canonic(universe.tuple(
					(SymbolicTupleType) this.dynamicType,
					new Singleton<SymbolicExpression>(universe.integer(-2))));
		case CHAR:
			return universe.character('\0');
		default:
		}
		return null;
	}

	@Override
	public TypeKind typeKind() {
		return TypeKind.PRIMITIVE;
	}
}
