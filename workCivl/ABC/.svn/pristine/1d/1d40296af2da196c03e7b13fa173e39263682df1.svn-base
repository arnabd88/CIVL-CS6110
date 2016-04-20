package edu.udel.cis.vsl.abc.ast.type.common;

import java.io.PrintStream;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import edu.udel.cis.vsl.abc.ast.node.IF.declaration.EnumeratorDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FieldDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.type.IF.ArithmeticType;
import edu.udel.cis.vsl.abc.ast.type.IF.ArrayType;
import edu.udel.cis.vsl.abc.ast.type.IF.AtomicType;
import edu.udel.cis.vsl.abc.ast.type.IF.DomainType;
import edu.udel.cis.vsl.abc.ast.type.IF.EnumerationType;
import edu.udel.cis.vsl.abc.ast.type.IF.Enumerator;
import edu.udel.cis.vsl.abc.ast.type.IF.Field;
import edu.udel.cis.vsl.abc.ast.type.IF.FloatingType;
import edu.udel.cis.vsl.abc.ast.type.IF.FloatingType.FloatKind;
import edu.udel.cis.vsl.abc.ast.type.IF.FunctionType;
import edu.udel.cis.vsl.abc.ast.type.IF.IntegerType;
import edu.udel.cis.vsl.abc.ast.type.IF.MemoryType;
import edu.udel.cis.vsl.abc.ast.type.IF.ObjectType;
import edu.udel.cis.vsl.abc.ast.type.IF.PointerType;
import edu.udel.cis.vsl.abc.ast.type.IF.QualifiedObjectType;
import edu.udel.cis.vsl.abc.ast.type.IF.SignedIntegerType;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType.BasicTypeKind;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardSignedIntegerType;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardSignedIntegerType.SignedIntKind;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardUnsignedIntegerType;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardUnsignedIntegerType.UnsignedIntKind;
import edu.udel.cis.vsl.abc.ast.type.IF.StructureOrUnionType;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;
import edu.udel.cis.vsl.abc.ast.type.IF.Type.TypeKind;
import edu.udel.cis.vsl.abc.ast.type.IF.TypeFactory;
import edu.udel.cis.vsl.abc.ast.type.IF.UnqualifiedObjectType;
import edu.udel.cis.vsl.abc.ast.type.IF.UnsignedIntegerType;
import edu.udel.cis.vsl.abc.ast.value.IF.IntegerValue;
import edu.udel.cis.vsl.abc.ast.value.IF.Value;

/**
 * An implementation of TypeFactory. The Flyweight Pattern is used on Types so
 * that, to the extent possible, two types will be equal iff they are the same
 * object.
 * 
 * @author siegel
 * 
 */
public class CommonTypeFactory implements TypeFactory {

	/**
	 * Minimum value of CHAR_BITS, the number of bits for the smallest object
	 * that is not a bit-field (i.e., one byte).
	 */
	public static final BigInteger CHAR_BIT_MIN = new BigInteger("8");

	private Map<Type, Type> typeMap = new LinkedHashMap<Type, Type>();

	private ArrayList<Type> typeList = new ArrayList<Type>();

	private ObjectType voidType = null;

	private ObjectType processType = null;

	private ObjectType heapType = null;

	private MemoryType memoryType = null;

	private ObjectType scopeType = null;

	private DomainType domainType = null;

	private ObjectType rangeType = null;

	private UnsignedIntegerType size_t = null, char16_t = null,
			char32_t = null;

	private SignedIntegerType ptrdiff_t = null;

	private IntegerType wchar_t = null;

	public CommonTypeFactory() {

	}

	private void insert(Type type) {
		((CommonType) type).setId(typeMap.size());
		typeMap.put(type, type);
		typeList.add(type);

		// Debugging:

		// System.out.println("Adding type: "+type.toString());
		// System.out.flush();

	}

	private Type canonicalize(Type type) {
		Type result = typeMap.get(type);

		if (result == null) {
			insert(type);
			return type;
		} else {
			return result;
		}
	}

	@Override
	public StandardBasicType basicType(BasicTypeKind kind) {
		StandardBasicType result;

		switch (kind) {
		case CHAR:
			result = new CommonCharType();
			break;
		case SIGNED_CHAR:
			result = new CommonStandardSignedIntegerType(
					SignedIntKind.SIGNED_CHAR);
			break;
		case UNSIGNED_CHAR:
			result = new CommonStandardUnsignedIntegerType(
					UnsignedIntKind.UNSIGNED_CHAR);
			break;
		case SHORT:
			result = new CommonStandardSignedIntegerType(SignedIntKind.SHORT);
			break;
		case UNSIGNED_SHORT:
			result = new CommonStandardUnsignedIntegerType(
					UnsignedIntKind.UNSIGNED_SHORT);
			break;
		case INT:
			result = new CommonStandardSignedIntegerType(SignedIntKind.INT);
			break;
		case UNSIGNED:
			result = new CommonStandardUnsignedIntegerType(
					UnsignedIntKind.UNSIGNED);
			break;
		case LONG:
			result = new CommonStandardSignedIntegerType(SignedIntKind.LONG);
			break;
		case UNSIGNED_LONG:
			result = new CommonStandardUnsignedIntegerType(
					UnsignedIntKind.UNSIGNED_LONG);
			break;
		case LONG_LONG:
			result = new CommonStandardSignedIntegerType(
					SignedIntKind.LONG_LONG);
			break;
		case UNSIGNED_LONG_LONG:
			result = new CommonStandardUnsignedIntegerType(
					UnsignedIntKind.UNSIGNED_LONG_LONG);
			break;
		case FLOAT:
			result = new CommonFloatingType(FloatKind.FLOAT, false);
			break;
		case DOUBLE:
			result = new CommonFloatingType(FloatKind.DOUBLE, false);
			break;
		case LONG_DOUBLE:
			result = new CommonFloatingType(FloatKind.LONG_DOUBLE, false);
			break;
		case REAL:
			result = new CommonFloatingType(FloatKind.REAL, false);
			break;
		case BOOL:
			result = new CommonStandardUnsignedIntegerType(UnsignedIntKind.BOOL);
			break;
		case FLOAT_COMPLEX:
			result = new CommonFloatingType(FloatKind.FLOAT, true);
			break;
		case DOUBLE_COMPLEX:
			result = new CommonFloatingType(FloatKind.DOUBLE, true);
			break;
		case LONG_DOUBLE_COMPLEX:
			result = new CommonFloatingType(FloatKind.LONG_DOUBLE, true);
			break;
		default:
			throw new RuntimeException("unreachable");
		}
		return (StandardBasicType) canonicalize(result);
	}

	@Override
	public StandardSignedIntegerType signedIntegerType(SignedIntKind kind) {
		return (StandardSignedIntegerType) canonicalize(new CommonStandardSignedIntegerType(
				kind));
	}

	@Override
	public StandardUnsignedIntegerType unsignedIntegerType(UnsignedIntKind kind) {
		return (StandardUnsignedIntegerType) canonicalize(new CommonStandardUnsignedIntegerType(
				kind));
	}

	@Override
	public FloatingType floatingType(FloatKind kind, boolean isReal) {
		if (isReal) {
			switch (kind) {
			case LONG_DOUBLE:
				return (FloatingType) basicType(BasicTypeKind.LONG_DOUBLE);
			case DOUBLE:
				return (FloatingType) basicType(BasicTypeKind.DOUBLE);
			case FLOAT:
				return (FloatingType) basicType(BasicTypeKind.FLOAT);
			default:
				throw new RuntimeException("unreachable");
			}
		} else {
			switch (kind) {
			case LONG_DOUBLE:
				return (FloatingType) basicType(BasicTypeKind.LONG_DOUBLE_COMPLEX);
			case DOUBLE:
				return (FloatingType) basicType(BasicTypeKind.DOUBLE_COMPLEX);
			case FLOAT:
				return (FloatingType) basicType(BasicTypeKind.FLOAT_COMPLEX);
			default:
				throw new RuntimeException("unreachable");
			}
		}

	}

	@Override
	public ObjectType voidType() {
		if (voidType == null) {
			voidType = new CommonVoidType();
			insert(voidType);
		}
		return voidType;

	}

	@Override
	public PointerType pointerType(Type referencedType) {
		return (PointerType) canonicalize(new CommonPointerType(referencedType));
	}

	@Override
	public AtomicType atomicType(UnqualifiedObjectType baseType) {
		return (AtomicType) canonicalize(new CommonAtomicType(baseType));
	}

	@Override
	public ArrayType incompleteArrayType(ObjectType elementType) {
		return (ArrayType) canonicalize(new CommonArrayType(elementType, false));
	}

	@Override
	public ArrayType unspecifiedVariableLengthArrayType(ObjectType elementType) {
		return (ArrayType) canonicalize(new CommonArrayType(elementType, true));
	}

	@Override
	public ArrayType variableLengthArrayType(ObjectType elementType,
			ExpressionNode variableSize) {
		return (ArrayType) canonicalize(new CommonArrayType(elementType,
				variableSize));
	}

	@Override
	public ArrayType arrayType(ObjectType elementType, IntegerValue constantSize) {
		return (ArrayType) canonicalize(new CommonArrayType(elementType,
				constantSize));
	}

	@Override
	public StructureOrUnionType structureOrUnionType(Object key,
			boolean isStruct, String tag) {
		StructureOrUnionType result = new CommonStructureOrUnionType(key, tag,
				isStruct);

		return (StructureOrUnionType) canonicalize(result);
	}

	@Override
	public Field newField(FieldDeclarationNode declaration, ObjectType type,
			Value bitWidth) {
		return new CommonField(declaration, type, bitWidth);
	}

	@Override
	public EnumerationType enumerationType(Object key, String tag) {
		EnumerationType result = new CommonEnumerationType(key, tag);

		return (EnumerationType) canonicalize(result);
	}

	@Override
	public Enumerator newEnumerator(EnumeratorDeclarationNode declaration,
			EnumerationType enumeration, Value value) {
		return new CommonEnumerator(declaration, enumeration, value);
	}

	@Override
	public ObjectType rangeType() {
		if (rangeType == null) {
			rangeType = new CommonRangeType();
			insert(rangeType);
		}
		return rangeType;
	}

	@Override
	public DomainType domainType() {
		if (domainType == null) {
			domainType = new CommonDomainType();
			insert(domainType);
		}
		return domainType;
	}

	@Override
	public DomainType domainType(int dimension) {
		DomainType result = new CommonDomainType(dimension);

		return (DomainType) canonicalize(result);
	}

	@Override
	public Type compositeType(Type type1, Type type2) {
		TypeKind kind = type1.kind();
		if (kind == TypeKind.ARRAY)
			return compositeArrayType((ArrayType) type1, (ArrayType) type2);
		else if (kind == TypeKind.FUNCTION)
			return compositeFunctionType((FunctionType) type1,
					(FunctionType) type2);
		else
			return type1;
	}

	/**
	 * 
	 * "If both types are array types, the following rules are applied: * If one
	 * type is an array of known constant size, the composite type is an array
	 * of that size. * Otherwise, if one type is a variable length array whose
	 * size is specified by an expression that is not evaluated, the behavior is
	 * undefined. * Otherwise, if one type is a variable length array whose size
	 * is specified, the composite type is a variable length array of that size.
	 * * Otherwise, if one type is a variable length array of unspecified size,
	 * the composite type is a variable length array of unspecified size. *
	 * Otherwise, both types are arrays of unknown size and the composite type
	 * is an array of unknown size. The element type of the composite type is
	 * the composite type of the two element types."
	 * 
	 * I'm not sure why you would not want to evaluate the size expression. It
	 * seems to refer to this:
	 * 
	 * "Where a size expression is part of the operand of a sizeof operator and
	 * changing the value of the size expression would not affect the result of
	 * the operator, it is unspecified whether or not the size expression is
	 * evaluated."
	 * 
	 * I can't think of an example where the changing the size expression would
	 * not affect the result of the operator.
	 * 
	 * @param type1
	 * @param type2
	 * @return
	 */
	private ArrayType compositeArrayType(ArrayType type1, ArrayType type2) {
		ObjectType elementType = (ObjectType) compositeType(
				type1.getElementType(), type2.getElementType());
		IntegerValue constantSize1 = type1.getConstantSize(), constantSize2;
		ExpressionNode sizeExpression1, sizeExpression2;

		if (constantSize1 != null)
			return arrayType(elementType, constantSize1);
		constantSize2 = type2.getConstantSize();
		if (constantSize2 != null) {
			return arrayType(elementType, constantSize2);
		}
		sizeExpression1 = type1.getVariableSize();
		if (sizeExpression1 != null)
			return variableLengthArrayType(elementType, sizeExpression1);
		sizeExpression2 = type2.getVariableSize();
		if (sizeExpression2 != null)
			return variableLengthArrayType(elementType, sizeExpression2);
		if (type1.hasUnspecifiedVariableLength()
				|| type2.hasUnspecifiedVariableLength())
			return unspecifiedVariableLengthArrayType(elementType);
		return incompleteArrayType(elementType);
	}

	private ObjectType returnType(FunctionType type1, FunctionType type2) {
		return (ObjectType) compositeType(type1.getReturnType(),
				type2.getReturnType());
	}

	private FunctionType extractParameterTypes(FunctionType type,
			ObjectType returnType) {
		return functionType(returnType, type.fromIdentifierList(),
				type.getParameterTypes(), type.hasVariableArgs());
	}

	private FunctionType merge(FunctionType type1, FunctionType type2) {
		List<ObjectType> parameterTypes = new LinkedList<ObjectType>();
		int numParameters = type1.getNumParameters();

		for (int i = 0; i < numParameters; i++)
			parameterTypes.add((ObjectType) compositeType(
					type1.getParameterType(i), type2.getParameterType(i)));
		return functionType(returnType(type1, type2),
				type1.fromIdentifierList(), parameterTypes,
				type1.hasVariableArgs());
	}

	/**
	 * "If only one type is a function type with a parameter type list (a
	 * function prototype), the composite type is a function prototype with the
	 * parameter type list."
	 * 
	 * "If both types are function types with parameter type lists, the type of
	 * each parameter in the composite parameter type list is the composite type
	 * of the corresponding parameters."
	 * 
	 * I assume the return type is the composite type of the two return types.
	 * 
	 * @param type1
	 *            a function type
	 * @param type2
	 *            a function type compatible with type1
	 * @return a composite type
	 */
	private FunctionType compositeFunctionType(FunctionType type1,
			FunctionType type2) {
		if (!type1.fromIdentifierList() && type2.fromIdentifierList())
			return extractParameterTypes(type1, returnType(type1, type2));
		if (!type2.fromIdentifierList() && type1.fromIdentifierList())
			return extractParameterTypes(type2, returnType(type1, type2));
		if (!type1.fromIdentifierList() && !type2.fromIdentifierList())
			return merge(type1, type2);
		if (!type1.parametersKnown() && !type2.parametersKnown())
			return functionType(returnType(type1, type2));
		if (type1.parametersKnown())
			return extractParameterTypes(type1, returnType(type1, type2));
		if (type2.parametersKnown())
			return extractParameterTypes(type2, returnType(type1, type2));
		return null;
	}

	@Override
	public FunctionType functionType(ObjectType returnType) {
		return (FunctionType) canonicalize(new CommonFunctionType(returnType));
	}

	@Override
	public FunctionType functionType(ObjectType returnType,
			boolean fromIdentifierList, Iterable<ObjectType> parameterTypes,
			boolean hasVariableArgs) {
		return (FunctionType) canonicalize(new CommonFunctionType(returnType,
				fromIdentifierList, parameterTypes, hasVariableArgs));
	}

	@Override
	public QualifiedObjectType qualifiedType(UnqualifiedObjectType baseType,
			boolean constQualified, boolean volatileQualified,
			boolean restrictQualified, boolean inputQualified,
			boolean outputQualified) {
		return (QualifiedObjectType) canonicalize(new CommonQualifiedObjectType(
				baseType, constQualified, volatileQualified, restrictQualified,
				inputQualified, outputQualified));
	}

	@Override
	public ObjectType qualify(ObjectType startType, boolean constQualified,
			boolean volatileQualified, boolean restrictQualified,
			boolean inputQualified, boolean outputQualified) {
		if (!constQualified && !volatileQualified && !restrictQualified)
			return startType;
		if (startType.kind() == TypeKind.QUALIFIED) {
			QualifiedObjectType qualifiedType = (QualifiedObjectType) startType;
			UnqualifiedObjectType unqualifiedType = qualifiedType.getBaseType();

			return qualifiedType(unqualifiedType, constQualified
					|| qualifiedType.isConstQualified(), volatileQualified
					|| qualifiedType.isVolatileQualified(), restrictQualified
					|| qualifiedType.isRestrictQualified(), inputQualified
					|| qualifiedType.isInputQualified(), outputQualified
					|| qualifiedType.isOutputQualified());
		}
		return qualifiedType((UnqualifiedObjectType) startType, constQualified,
				volatileQualified, restrictQualified, inputQualified,
				outputQualified);
	}

	@Override
	public ObjectType qualify(ObjectType startType, boolean atomic,
			boolean constQualified, boolean volatileQualified,
			boolean restrictQualified, boolean inputQualified,
			boolean outputQualified) {
		boolean change = false;
		UnqualifiedObjectType baseType;

		if (startType instanceof QualifiedObjectType) {
			QualifiedObjectType qualifiedType = (QualifiedObjectType) startType;

			baseType = qualifiedType.getBaseType();
			if (qualifiedType.isConstQualified())
				constQualified = true;
			else if (constQualified)
				change = true;
			if (qualifiedType.isVolatileQualified())
				volatileQualified = true;
			else if (volatileQualified)
				change = true;
			if (qualifiedType.isRestrictQualified())
				restrictQualified = true;
			else if (restrictQualified)
				change = true;
			if (qualifiedType.isInputQualified())
				inputQualified = true;
			else if (inputQualified)
				change = true;
			if (qualifiedType.isOutputQualified())
				outputQualified = true;
			else if (outputQualified)
				change = true;
		} else {
			baseType = (UnqualifiedObjectType) startType;
			change = constQualified || volatileQualified || restrictQualified;
		}
		if (atomic && !(baseType instanceof AtomicType)) {
			baseType = atomicType(baseType);
			change = true;
		}
		if (!change)
			return startType;
		if (constQualified || restrictQualified || volatileQualified)
			return qualifiedType(baseType, constQualified, volatileQualified,
					restrictQualified, inputQualified, outputQualified);
		return baseType;
	}

	@Override
	public int getNumTypes() {
		return typeMap.size();
	}

	@Override
	public Type getType(int id) {
		return typeList.get(id);
	}

	@Override
	public Iterable<Type> getTypes() {
		return typeMap.keySet();
	}

	@Override
	public void printTypes(PrintStream out) {
		printTypes("", out);
	}

	public void printTypes(String prefix, PrintStream out) {
		for (Type type : typeList) {
			out.print(prefix + type.getId() + ": ");
			type.print(prefix, out, false);
			out.println();
		}
		out.flush();
	}

	@Override
	public IntegerType integerPromotion(IntegerType type) {
		if (type instanceof StandardSignedIntegerType) {
			SignedIntKind kind = ((StandardSignedIntegerType) type)
					.getIntKind();

			switch (kind) {
			case SIGNED_CHAR:
			case SHORT:
				return signedIntegerType(SignedIntKind.INT);
			case INT:
			case LONG:
			case LONG_LONG:
				return type;
			default:
				throw new RuntimeException("unreachable");
			}
		}
		if (type instanceof StandardUnsignedIntegerType) {
			UnsignedIntKind kind = ((StandardUnsignedIntegerType) type)
					.getIntKind();

			switch (kind) {
			case BOOL:
				return signedIntegerType(SignedIntKind.INT);
			case UNSIGNED_CHAR:
			case UNSIGNED_SHORT:
				// either int or unsigned int, depending on widths
				return (IntegerType) canonicalize(new IntegerPromotionType(type));
			case UNSIGNED:
			case UNSIGNED_LONG:
			case UNSIGNED_LONG_LONG:
				return type;
			default:
				throw new RuntimeException("unreachable");
			}
		}
		// enumeration type: no way to know compatible integer type
		return (IntegerType) canonicalize(new IntegerPromotionType(type));
	}

	@Override
	public ArithmeticType usualArithmeticConversion(ArithmeticType type1,
			ArithmeticType type2) {
		// if (type1.equals(type2))
		// return type1;
		// else {
		ArithmeticType result = floatingArithmeticConversion(type1, type2);

		if (result != null)
			return result;
		if (!type1.isInteger())
			throw new RuntimeException("Unexpected arithmetic type: " + type1);
		if (!type2.isInteger())
			throw new RuntimeException("Unexpected arithmetic type: " + type2);

		IntegerType intType1 = integerPromotion((IntegerType) type1);
		IntegerType intType2 = integerPromotion((IntegerType) type2);

		if (intType1.equals(intType2))
			return intType1;
		return integerArithmeticConversion(intType1, intType2);
		// }
	}

	/**
	 * Returns the usual arithmetic conversion type in the case where at least
	 * one of the two types is a floating type. If neither is a floating type,
	 * returns null.
	 * 
	 * @param type1
	 *            an arithmetic type
	 * @param type2
	 *            an arithmetic type
	 * @return null (if neither type is floating) or the floating type which is
	 *         the usual arithmetic conversion type if at least one of the types
	 *         is floating
	 */
	private FloatingType floatingArithmeticConversion(ArithmeticType type1,
			ArithmeticType type2) {
		boolean isFloat1 = type1.isFloating();
		boolean isFloat2 = type2.isFloating();

		if (!isFloat1 && !isFloat2) {
			return null;
		} else {
			FloatingType float1 = null, float2 = null;
			FloatKind kind1 = null, kind2 = null, kind;

			if (isFloat1) {
				float1 = (FloatingType) type1;
				kind1 = float1.getFloatKind();
			}
			if (isFloat2) {
				float2 = (FloatingType) type2;
				kind2 = float2.getFloatKind();
			}
			if (kind1 == FloatKind.LONG_DOUBLE)
				kind = kind1;
			else if (kind2 == FloatKind.LONG_DOUBLE)
				kind = kind2;
			else if (kind1 == FloatKind.DOUBLE)
				kind = kind1;
			else if (kind2 == FloatKind.DOUBLE)
				kind = kind2;
			else if (kind1 == FloatKind.FLOAT)
				kind = kind1;
			else if (kind2 == FloatKind.FLOAT)
				kind = kind2;
			else
				throw new RuntimeException("unreachable");
			return floatingType(kind,
					type1.inRealDomain() && type2.inRealDomain());
		}
	}

	private IntegerType integerArithmeticConversion(IntegerType type1,
			IntegerType type2) {

		if (type1.equals(type2))
			return type1;
		else {
			boolean isSigned1 = type1 instanceof SignedIntegerType;
			boolean isSigned2 = type2 instanceof SignedIntegerType;
			boolean isUnsigned1 = type1 instanceof UnsignedIntegerType;
			boolean isUnsigned2 = type2 instanceof UnsignedIntegerType;

			if (isSigned1 && isSigned2 || isUnsigned1 && isUnsigned2) {
				// "no two signed integer types shall have the same rank"
				int rankComparison = compareConversionRanks(type1, type2);

				if (rankComparison == -1)
					return type2;
				if (rankComparison == 1)
					return type1;
				if (rankComparison == 0)
					throw new RuntimeException(
							"Internal error: two different unsigned integer types "
									+ "have same conversion rank:\n" + type1
									+ "\n" + type2);
			} else if (isSigned1 && isUnsigned2 || isSigned2 && isUnsigned1) {
				IntegerType signedType = (isSigned1 ? type1 : type2);
				IntegerType unsignedType = (isUnsigned1 ? type1 : type2);
				int rankComparison = compareConversionRanks(signedType,
						unsignedType);

				if (rankComparison == -1 || rankComparison == 0) {
					return unsignedType;
				}
			}
			return (ArithmeticConversionType) canonicalize(new ArithmeticConversionType(
					type1, type2));
		}
	}

	@Override
	public IntegerType rangeChoice(BigInteger value, IntegerType type1,
			IntegerType type2) {
		if (alwaysInRange(value, type1))
			return type1;
		return new RangeChoiceType(value, type1, type2);
	}

	@Override
	public IntegerType rangeChoice(BigInteger value, IntegerType[] typeList) {
		return rangeChoice(value, typeList, 0);
	}

	public IntegerType rangeChoice(int value, IntegerType type1,
			IntegerType type2) {
		return rangeChoice(new BigInteger("" + value), type1, type2);
	}

	private boolean alwaysInRange(BigInteger value, IntegerType type) {
		if (type instanceof StandardSignedIntegerType) {
			StandardSignedIntegerType stype = (StandardSignedIntegerType) type;

			if (value.compareTo(stype.getMinimumMinValue()) >= 0
					&& value.compareTo(stype.getMinimumMaxValue()) <= 0)
				return true;
		} else if (type instanceof StandardUnsignedIntegerType) {
			if (value.signum() >= 0
					&& value.compareTo(((StandardUnsignedIntegerType) type)
							.getMinimumMaxValue()) <= 0)
				return true;
		} else if (type instanceof StandardBasicType
				&& ((StandardBasicType) type).getBasicTypeKind() == BasicTypeKind.CHAR) {
			if (value.signum() >= 0
					&& value.compareTo(CommonStandardSignedIntegerType.SCHAR_MAX_MIN) <= 0)
				return true;
		}
		return false;
	}

	private IntegerType rangeChoice(BigInteger value, IntegerType[] typeList,
			int index) {
		IntegerType type1 = typeList[index];

		if (alwaysInRange(value, type1))
			return type1;
		if (index == typeList.length - 1)
			return new RangeChoiceType(value, type1, null);
		return new RangeChoiceType(value, type1, rangeChoice(value, typeList,
				index + 1));
	}

	@Override
	public SignedIntegerType ptrdiff_t() {
		if (ptrdiff_t == null) {
			ptrdiff_t = new SymbolicSignedIntegerType("ptrdiff_t");
			insert(ptrdiff_t);
		}
		return ptrdiff_t;
	}

	@Override
	public UnsignedIntegerType size_t() {
		if (size_t == null) {
			size_t = new SymbolicUnsignedIntegerType("size_t");
			insert(size_t);
		}
		return size_t;
	}

	@Override
	public IntegerType wchar_t() {
		if (wchar_t == null) {
			wchar_t = new SymbolicIntegerType("wchar_t");
			insert(wchar_t);
		}
		return wchar_t;
	}

	@Override
	public UnsignedIntegerType char16_t() {
		if (char16_t == null) {
			char16_t = new SymbolicUnsignedIntegerType("char16_t");
			insert(char16_t);
		}
		return char16_t;
	}

	@Override
	public UnsignedIntegerType char32_t() {
		if (char32_t == null) {
			char32_t = new SymbolicUnsignedIntegerType("char32_t");
			insert(char32_t);
		}
		return char32_t;
	}

	/**
	 * Attempts to integer compare conversion ranks and return a definitive
	 * result, but may return "don't know". Possible return values and their
	 * meaning:
	 * 
	 * <ul>
	 * <li>-1: rank(type1) is less than rank(type2)</li>
	 * <li>0: rank(type1) equals rank(type2)</li>
	 * <li>+1: rank(type1) is greater than rank(type2)</li>
	 * <li>any other number: don't know</li>
	 * </ul>
	 * 
	 * @param type1
	 * @param type2
	 * @return
	 */
	private int compareConversionRanks(IntegerType type1, IntegerType type2) {
		Integer rank1 = conversionRank(type1);
		Integer rank2 = conversionRank(type2);

		if (rank1 != null && rank2 != null) {
			int difference = rank1 - rank2;

			if (difference == 0)
				return 0;
			if (difference < 0)
				return -1;
			return 1;
		}
		return 2;
	}

	private Integer conversionRank(IntegerType type) {
		if (type instanceof StandardBasicType) {
			BasicTypeKind kind = ((StandardBasicType) type).getBasicTypeKind();

			switch (kind) {
			case BOOL:
				return 1;
			case CHAR:
			case SIGNED_CHAR:
			case UNSIGNED_CHAR:
				return 2;
			case SHORT:
			case UNSIGNED_SHORT:
				return 3;
			case INT:
			case UNSIGNED:
				return 4;
			case LONG:
			case UNSIGNED_LONG:
				return 5;
			case LONG_LONG:
			case UNSIGNED_LONG_LONG:
				return 6;
			default:
				throw new RuntimeException("Unexpected basic integer type: "
						+ type);
			}
		}
		return null;
	}

	@Override
	public ObjectType processType() {
		if (processType == null) {
			processType = new CommonProcessType();
			insert(processType);
		}
		return processType;
	}

	@Override
	public ObjectType heapType() {
		if (heapType == null) {
			heapType = new CommonHeapType();
			insert(heapType);
		}
		return heapType;
	}

	@Override
	public MemoryType memoryType() {
		if (memoryType == null) {
			memoryType = new CommonMemoryType();
			insert(memoryType);
		}
		return memoryType;
	}

	@Override
	public ObjectType scopeType() {
		if (scopeType == null) {
			scopeType = new CommonScopeType();
			insert(scopeType);
		}
		return scopeType;
	}

	@Override
	public boolean isArrayOfCharType(Type type) {
		if (type instanceof ArrayType) {
			ObjectType elementType = ((ArrayType) type).getElementType();

			if (elementType instanceof StandardBasicType) {
				return ((StandardBasicType) elementType).getBasicTypeKind() == BasicTypeKind.CHAR;
			}
		}
		return false;
	}

	@Override
	public boolean isVoidType(Type type) {
		return type instanceof CommonVoidType;
	}

	@Override
	public boolean isBundleType(Type type) {
		if (type instanceof StructureOrUnionType) {
			StructureOrUnionType structOrUnionType = (StructureOrUnionType) type;

			if (structOrUnionType.isStruct()
					&& structOrUnionType.getName().equals(TypeFactory.BUNDLE)) {
				return true;
			}
		}
		return false;
	}
}
