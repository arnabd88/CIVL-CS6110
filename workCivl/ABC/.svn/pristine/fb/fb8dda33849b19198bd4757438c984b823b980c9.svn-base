package edu.udel.cis.vsl.abc.ast.type.IF;

import java.io.PrintStream;
import java.math.BigInteger;

import edu.udel.cis.vsl.abc.ast.entity.IF.Entity;
import edu.udel.cis.vsl.abc.ast.entity.IF.Label;
import edu.udel.cis.vsl.abc.ast.entity.IF.Variable;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.EnumeratorDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FieldDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.type.IF.FloatingType.FloatKind;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType.BasicTypeKind;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardSignedIntegerType.SignedIntKind;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardUnsignedIntegerType.UnsignedIntKind;
import edu.udel.cis.vsl.abc.ast.value.IF.IntegerValue;
import edu.udel.cis.vsl.abc.ast.value.IF.Value;

/**
 * <p>
 * A factory for producing C types, which are represented as instances of
 * {@link Type}. C types are complicated. First, types have state which may
 * change during compile-time processing of the translation unit. For example,
 * at any point in the translation unit, an object type is either complete or
 * incomplete, and this may change. Example:
 * 
 * <pre>
 * typedef struct Node {
 *   struct Node *next;
 * } list;
 * </pre>
 * 
 * Immediately after the <code>struct Node</code> the structure type exists, but
 * is incomplete. It becomes complete immediately after the <code>}</code>.
 * </p>
 * 
 * <p>
 * A {@link Type} may be associated to an {@link Entity} (more precisely, to any
 * {@link Entity} other than a {@link Label}). The type associated to an
 * {@link Entity} may change as declarations of that {@link Entity} are
 * processed.
 * </p>
 * 
 * <p>
 * {@link Type}s are immutable, with the following exception: a tagged type
 * (instance of {@link StructureOrUnionType} or {@link EnumerationType}) may
 * start off as incomplete and later be completed. Hence any other types that
 * have a reference to that tagged type will also reflect the change. On the
 * other hand, an array declared with an incomplete type, such as
 * <code>int a[]</code> and later declared with a complete type such as
 * <code>int a[5]</code> does <strong>not</strong> result in a modifcation to
 * the {@link ArrayType} object. Instead, the type associated to the
 * {@link Variable} named <code>a</code> is changed from the incomplete type
 * <code>int[]</code> to the complete type <code>int[5]</code>.
 * </p>
 * 
 * <p>
 * There are two kinds of types: function and object types. These are
 * represented by two interfaces, {@link FunctionType} and {@link ObjectType},
 * each of which extends {@link Type}.
 * </p>
 * 
 * <p>
 * Detailed information on specified types:
 * </p>
 * 
 * <p>
 * {@link ArrayType}: this is an object type specified by an element type and
 * the extent. The element type must be a complete object type. For the extent,
 * there are 4 possibilities:
 * 
 * <ol>
 * <li>the extent is not specified (i.e., is <code>null</code>): then the array
 * type is an <strong>incomplete type</strong>. It becomes complete when the
 * extent is specified in a later declaration.</li>
 * 
 * <li>the extent is <code>*</code>: this is a <strong>VLA type of unspecified
 * size</strong>. It is nevertheless a complete type. This can only be used in
 * declarations or type names in function prototype scope (i.e., in a function
 * declaration that is not part of a function definition).</li>
 * 
 * <li>the extent is an integer constant expression <strong>and</strong> the
 * element type has known constant size: then the array type is <strong>not a
 * VLA</strong> type. It is complete.</li>
 * 
 * <li>otherwise, the extent is an expression which is not a constant expression
 * or the element type does not have known constant size. This is a <strong>VLA
 * type</strong>. It is complete. If it occurs in function prototype scope, it
 * is replaced by <code>*</code> (i.e., the expression is not used).</li>
 * </ol>
 * </p>
 * 
 * <p>
 * Some vocabulary:
 * <ul>
 * <li>An object type has <strong>known constant size</strong> iff it is not
 * incomplete <strong>and</strong> not a VLA (Variable Length Array) type.</li>
 * 
 * <li>A <strong>variably modified</strong> (VM) type is a declarator type which
 * in the nested sequence of declarators has a VLA type, or any type derived
 * from a VM type. I.e.: a VLA is a VM; a pointer to a VM is a VM; a function
 * returning a VM is a VM; an array with a VM element type is a VM.</li>
 * </ul>
 * </p>
 * 
 * <p>
 * Some restrictions:
 * <ul>
 * <li>An identifier declared with a VM type must be an object, be an ordinary
 * identifier, have no linkage, and have either block or function prototype
 * scope.</li>
 * <li>An object declared with static or thread storage duration shall not have
 * a VLA type (but may have a VM type).</li>
 * <li>Pointer types are always complete object types (even if the referenced
 * type is not).</li>
 * </ul>
 * </p>
 * 
 * <p>
 * A structure or union type exists (come into scope) as soon as the tag name
 * first appears, but is incomplete until the <code>}</code> is reached, then it
 * is complete. The last member may be an incomplete array type. Members must
 * have object types and cannot have VM types.
 * </p>
 * 
 * <p>
 * Enumeration types: complete once <code>}</code> is reached.
 * </p>
 * 
 * <p>
 * Atomic types: the base type cannot be array, function, atomic, or qualified.
 * </p>
 * 
 * <p>
 * <code>void</code>: is an incomplete object type that can never be completed.
 * </p>
 * 
 * <p>
 * Function Types: a function type is specified by the return type and types of
 * the parameters. In function <strong>definitions</strong>: the parameter types
 * (after adjustment) cannot be incomplete. Hence once you get to the
 * definition, all parameter types must be complete (or an exception will be
 * thrown). The adjustments: a parameter of type qualified array of T is changed
 * to qualified pointer to T; qualified function returning T changed to
 * qualified pointer to function returning T.
 * </p>
 * 
 * <p>
 * Qualifiers:
 * <ul>
 * <li>A type can come with qualifiers: <code>const</code>,
 * <code>restrict</code>, <code>volatile</code>, <code>_Atomic</code>.</li>
 * 
 * <li>If the specification of an array type includes any type qualifiers, the
 * element type is so-qualified, not the array type. If the specification of a
 * function type includes any type qualifiers, the behavior is undefined. [Both
 * can happen through typedefs.] Moreover, <code>restrict</code> can only be
 * used with pointer types whose referenced type is an object type.
 * <code>_Atomic</code> can not be used with an array or function type.</li>
 * 
 * <li>If the <code>_Atomic</code> qualifier occurs (possibly with other
 * qualifiers), the result is the so-qualified Atomic type.</li>
 * </ul>
 * </p>
 * 
 * <p>
 * See C11 Sec. 5.2.4.2.1 for the minimum values of the bounds for each standard
 * integer type.
 * </p>
 * 
 * @author siegel
 * 
 */
public interface TypeFactory {

	public static String BUNDLE = "$bundle";

	/**
	 * Returns an instance of BasicType representing the type of the given basic
	 * type kind and qualified as specified.
	 * 
	 * It is unspecified whether this method will return a new instance each
	 * time it is invoked, or will use something like a flyweight pattern to
	 * share instances. This choice should be invisible to the user, since the
	 * basic types are immutable.
	 * 
	 * @param kind
	 *            one of the basic type kinds
	 * @return an instance of BasicType corresponding to the given parameters
	 */
	StandardBasicType basicType(BasicTypeKind kind);

	/**
	 * Returns the standard signed integer type of the given kind. While these
	 * types are all basic types and can therefore be obtained by method
	 * basicType, this method is sometimes more convenient.
	 * 
	 * There are 5 standard signed integer types.
	 * 
	 * @param kind
	 *            the signed integer type kind; note that the names of the
	 *            elements of this enumerated type are exactly the same as the
	 *            names of the corresponding types in BasicTypeKind
	 * @return the signed integer type of that kind
	 */
	StandardSignedIntegerType signedIntegerType(SignedIntKind kind);

	/**
	 * Returns the standard unsigned integer type of the given kind. While these
	 * types are all basic types and can therefore be obtained by method
	 * basicType, this method is sometimes more convenient.
	 * 
	 * There are 6 standard unsigned integer types (those corresponding to the
	 * standard signed integer types, and _Bool).
	 * 
	 * @param kind
	 *            the unsigned integer type kind; note that the names of the
	 *            elements of this enumerated type are exactly the same as the
	 *            names of the corresponding types in BasicTypeKind
	 * @return the unsigned integer type of that kind
	 */
	StandardUnsignedIntegerType unsignedIntegerType(UnsignedIntKind kind);

	/**
	 * Returns an instance of PointerType with the given referenced type. It is
	 * unspecified whether this returns a new instance each time it is called or
	 * can return previously returned instances.
	 * 
	 * @param referencedType
	 *            the base type of the pointer type
	 * @return a pointer type as specified
	 */
	PointerType pointerType(Type referencedType);

	/**
	 * The atomic type associated to a base type. This type may be denoted
	 * <code>_Atomic(baseType)</code> or by using the type qualifier
	 * <code>_Atomic</code> in a declaration. The base type cannot be an array
	 * type, a function type, an atomic type, or a qualified type. However, the
	 * resulting AtomicType can be qualified.
	 * 
	 * @param baseType
	 *            the base type
	 * @return the atomic type
	 */
	AtomicType atomicType(UnqualifiedObjectType baseType);

	/**
	 * Returns an incomplete array type (i.e., the extent is not specified).
	 * 
	 * Note: according to the C standard, qualifiers applied to an array type
	 * are actually applied to the element type.
	 * 
	 * @param elementType
	 *            a complete object type
	 * @return an incomplete array type with given element type
	 */
	ArrayType incompleteArrayType(ObjectType elementType);

	/**
	 * Returns a complete array type in which the size expression has been
	 * evaluated to a known constant value.
	 * 
	 * @param elementType
	 *            the type of the elements of the array
	 * @param constantExtent
	 *            the constant array length
	 * @return the complete array type with constant extent
	 */
	ArrayType arrayType(ObjectType elementType, IntegerValue constantExtent);

	/**
	 * Returns a complete array type of "unspecified variable length". This is
	 * declared using a "*" for the size expression. This can only be used in
	 * function prototype scope.
	 * 
	 * @param elementType
	 * @return complete array type of unspecified variable length
	 */
	ArrayType unspecifiedVariableLengthArrayType(ObjectType elementType);

	/**
	 * Returns a complete array type in which the size expression cannot be
	 * evaluated to a known constant value.
	 * 
	 * @param elementType
	 *            the type of the elements of the array
	 * @param variableSize
	 *            the expression which defines the extent (length) of the array
	 * @return a complete array type as specified
	 */
	ArrayType variableLengthArrayType(ObjectType elementType,
			ExpressionNode variableSize);

	/**
	 * Returns a new incomplete structure or union type with the given tag. The
	 * type can be completed using methods in the resulting StructureOrUnionType
	 * object.
	 * 
	 * @param key
	 *            a key to use to determine if two StructureOrUnionType
	 *            instances with same tag and "isStruct" values are to be
	 *            considered equal.
	 * 
	 * @param isStruct
	 *            is this a structure type (as opposed to union)?
	 * @param tag
	 *            the tag for the structure or union, as in "struct TAG ...";
	 *            may be null for an anonymous structure or union
	 * @return a new, incomplete StructureOrUnion type
	 */
	StructureOrUnionType structureOrUnionType(Object key, boolean isStruct,
			String tag);

	/**
	 * Creates a new field entity. These correspond to the field declarations in
	 * a complete structure or union definition.
	 * 
	 * @param declaration
	 *            the field declaration
	 * @param type
	 *            the type of the field
	 * @param bitWidth
	 *            the optional bit width parameter
	 * @return the new field
	 */
	Field newField(FieldDeclarationNode declaration, ObjectType type,
			Value bitWidth);

	/**
	 * Returns an enumeration type with the given tag and key. The type can be
	 * completed using methods in the resulting EnumerationType object.
	 * 
	 * @param key
	 *            an object used to uniquely identify the enumeration type; it
	 *            is used in the equals method
	 * 
	 * @param tag
	 *            the tag for the enumeration type, as in "enum TAG ..."; may be
	 *            null for an anonymous enumeration type
	 * @return a new, incomplete enumeration type
	 */
	EnumerationType enumerationType(Object key, String tag);

	/**
	 * Creates a new enumerator entity. These correspond to the enumerators in
	 * the enumerator list of a complete enumeration definition.
	 * 
	 * @param declaration
	 *            the declaration of the enumerator in the enuemrator list
	 * @param enumeration
	 *            the enumeration of which this enumerator is a part
	 * @param value
	 *            the constant integer value associated to the enumerator
	 * @return the new enumerator entity
	 */
	Enumerator newEnumerator(EnumeratorDeclarationNode declaration,
			EnumerationType enumeration, Value value);

	/**
	 * Returns a qualified type based on the given unqualified type. At least
	 * one of the 3 qualifiers must be true.
	 * 
	 * @param baseType
	 *            an unqualified object type
	 * @param constQualified
	 *            should the resulting type be "const" qualified?
	 * @param volatileQualified
	 *            should the resulting type be "volatile" qualified?
	 * @param restrictQualified
	 *            should the resulting type be "restrict" qualified?
	 * @param inputQualified
	 *            should the result type be "_input" qualified?
	 * @param outputQualified
	 *            should the resulting type be "_output" qualified?
	 * @return qualified version of given unqualified type
	 */
	QualifiedObjectType qualifiedType(UnqualifiedObjectType baseType,
			boolean constQualified, boolean volatileQualified,
			boolean restrictQualified, boolean inputQualified,
			boolean outputQualified);

	/**
	 * A more general algorithm for qualifying a type: for each true-valued
	 * parameter, the corresponding qualifier is "added" to the resulting type,
	 * i.e., if the type is already so-qualified, it is not changed, otherwise,
	 * the result will be so qualified. The given type (startType) may or may
	 * not already be a QualifiedObjectType. The 3 boolean parameters may or may
	 * not be all false. The result may or may not be a QualifiedObjectType.
	 * 
	 * @param startType
	 *            an object type
	 * @param constQualified
	 *            should the resulting type be "const" qualified?
	 * @param volatileQualified
	 *            should the resulting type be "volatile" qualified?
	 * @param restrictQualified
	 *            should the resulting type be "restrict" qualified?
	 * @param inputQualified
	 *            should the result type be "_input" qualified?
	 * @param outputQualified
	 *            should the resulting type be "_output" qualified?
	 * @return the correct object type properly qualified, possibly the original
	 *         type as given.
	 */
	ObjectType qualify(ObjectType startType, boolean constQualified,
			boolean volatileQualified, boolean restrictQualified,
			boolean inputQualified, boolean outputQualified);

	/**
	 * Given two compatible types, returns the "composite type" obtained by
	 * combining features of both types. If the two types are not compatible,
	 * the behavior is undefined. Hence, you should always check compatibility
	 * before invoking this method (i.e., check that type1.compatibleWith(type2)
	 * is true).
	 * 
	 * Implementation: there are special rules for array and function types
	 * described in C11 Sec. 6.2.7(3). For all other types, the types have to be
	 * basically equivalent, so we just return type1.
	 * 
	 * @param type1
	 *            a type
	 * @param type2
	 *            a type which is compatible with type1
	 * @return the composite type
	 */
	Type compositeType(Type type1, Type type2);

	/**
	 * Returns the function type with the given return type but with no
	 * information on the parameters.
	 * 
	 * The return type cannot be an array type or a function type.
	 * 
	 * @param returnType
	 *            the return type of the function
	 * @return the function type
	 */
	FunctionType functionType(ObjectType returnType);

	/**
	 * Returns the function type with the given return type and parameter type
	 * list.
	 * 
	 * The return type cannot be an array type or a function type.
	 * 
	 * @param returnType
	 *            the type returned by calls to the function
	 * @param fromIdentifierList
	 *            was this type generated from a function definition using an
	 *            identifier list (as opposed to a parameter type list)?
	 * @param parameterTypes
	 *            the type of each parameter
	 * @param hasVariableArgs
	 *            is the "..." used in the declaration?
	 * @return a function type as specified in which the types of the parameters
	 *         is known
	 */
	FunctionType functionType(ObjectType returnType,
			boolean fromIdentifierList, Iterable<ObjectType> parameterTypes,
			boolean hasVariableArgs);

	/**
	 * Returns the number of distinct types controlled by this type factory.
	 * 
	 * @return the number of types conrolloed by this type factory
	 */
	int getNumTypes();

	/**
	 * Returns the id-th type conrolled by this type factory.
	 * 
	 * @param id
	 *            an int in the range [0,numTypes-1]
	 * @return the id-th type
	 */
	Type getType(int id);

	/**
	 * Returns the set of types controlled by this type factory as an Iterable
	 * object. The iterator will return the types in order of increasing ID.
	 * 
	 * @return sequence of types controlled by this type factory
	 */
	Iterable<Type> getTypes();

	/**
	 * Prints a human-readable description of all the types controlled by this
	 * type factory.
	 * 
	 * @param out
	 *            a print stream to which the output should be sent
	 */
	void printTypes(PrintStream out);

	/**
	 * C11 6.3.1.1:
	 * 
	 * <blockquote>
	 * <p>
	 * The following may be used in an expression wherever an int or unsigned
	 * int may be used:
	 * 
	 * <ul>
	 * <li>An object or expression with an integer type (other than int or
	 * unsigned int) whose integer conversion rank is less than or equal to the
	 * rank of int and unsigned int.</li>
	 * 
	 * <li>A bit-field of type _Bool, int, signed int, or unsigned int.</li>
	 * </ul>
	 * </p>
	 * 
	 * <p>
	 * If an int can represent all values of the original type (as restricted by
	 * the width, for a bit-field), the value is converted to an int; otherwise,
	 * it is converted to an unsigned int. These are called the integer
	 * promotions. All other types are unchanged by the integer promotions.
	 * </p>
	 * 
	 * <p>
	 * The integer promotions preserve value including sign. As discussed
	 * earlier, whether a "plain" char is treated as signed is
	 * implementation-defined.
	 * </p>
	 * </blockquote>
	 * 
	 * @param type
	 * @return the integer promotion
	 */
	IntegerType integerPromotion(IntegerType type);

	/**
	 * Returns a integer type object T with the following semantics: if the
	 * value falls within the range of type1, T represents type1, else T
	 * represents type2. These expressions can be nested to form a sequence of
	 * tests.
	 * 
	 * If it can be determined that value lies (resp., does not lie) in the
	 * range of type1 for all conforming C implementations, then this method may
	 * just return type1 (resp., type2).
	 * 
	 * @param value
	 *            an integer
	 * @param type1
	 *            an integer type
	 * @param type2
	 *            an integer type
	 * @return an integer type with the semantics described above
	 */
	IntegerType rangeChoice(BigInteger value, IntegerType type1,
			IntegerType type2);

	/**
	 * Returns an IntegerType T with the following semantics: if the value falls
	 * within the range of typeList[0] then typeList[0], else if the value falls
	 * within the range of typeList[1] then typeList[1], else if ...., else if
	 * the value falls within the range of typeList[n-1] then typeList[n-1],
	 * else null. Here, n=typeList.length.
	 * 
	 * @param value
	 *            an integer
	 * @param typeList
	 *            a sequence of integer types; it could have length 0, but this
	 *            would not be very useful (result is equivalent to null).
	 * @return an IntegerType with the semantics defined above.
	 */
	IntegerType rangeChoice(BigInteger value, IntegerType[] typeList);

	/**
	 * Returns the type size_t. The C Standard specified that every C
	 * implementation must define an unsigned integer type called size_t. It is
	 * the return type of the sizeof operator. It may or may not be one of the
	 * standard unsigned integer types.
	 * 
	 * Repeated calls to this method will always return the same type.
	 * 
	 * @return the unsigned integer type size_t.
	 */
	UnsignedIntegerType size_t();

	/**
	 * Returns the type ptrdiff_t,
	 * 
	 * <blockquote> which is the signed integer type of the result of
	 * subtracting two pointers; </blockquote>
	 * 
	 * (C11, Sec.7.19).
	 * 
	 * @return the signed integer type ptrdiff_t
	 */
	SignedIntegerType ptrdiff_t();

	/**
	 * Returns the type wchar_t:
	 * 
	 * <blockquote> an integer type whose range of values can represent distinct
	 * codes for all members of the largest extended character set specified
	 * among the supported locales; the null character shall have the code value
	 * zero. Each member of the basic character set shall have a code value
	 * equal to its value when used as the lone character in an integer
	 * character constant if an implementation does not define _
	 * _STDC_MB_MIGHT_NEQ_WC_ _. </blockquote>
	 * 
	 * (C11, Sec. 7.19).
	 * 
	 * @return the integer type wchar_t
	 */
	IntegerType wchar_t();

	/**
	 * Returns the type char16_t, "...an unsigned integer type used for 16-bit
	 * characters and is the same type as uint_least16_t (described in
	 * 7.20.1.2)", defined in Sec. 7.28, uchar.h.
	 * 
	 * @return the integer type char16_t
	 */
	UnsignedIntegerType char16_t();

	/**
	 * Returns the type char32_t, "...an unsigned integer type used for 32-bit
	 * characters and is the same type as uint_least32_t (also described in
	 * 7.20.1.2)."
	 * 
	 * @return the intger type char32_t
	 */
	UnsignedIntegerType char32_t();

	/**
	 * Returns an instance of ObjectType representing the "void" type. This is
	 * an incomplete object type which can never be completed. It is unspecified
	 * whether this method always returns a new instance or the same instance.
	 * The choice is invisible, since the type returned is immutable.
	 * 
	 * @return an instance of the void type
	 */
	ObjectType voidType();

	/**
	 * Returns the floating point type (real or complex) as specified. As these
	 * types are all standard basic types, they can also be obtained by method
	 * basicType, but this method is provided because it is more convenient in
	 * certain contexts.
	 * 
	 * @param kind
	 *            the kind of floating type: LONG_DOUBLE, DOUBLE, or FLOAT
	 *            (whether real or complex)
	 * @param isReal
	 *            is this a real type (not complex)?
	 * @return one of the basic types LONG_DOUBLE, DOUBLE, FLOAT,
	 *         LONG_DOUBLE_COMPLEX, DOUBLE_COMPLEX, or FLOAT_COMPLEX, as
	 *         specified
	 */
	FloatingType floatingType(FloatKind kind, boolean isReal);

	/** Returns the process type. */
	ObjectType processType();

	/** Returns the heap type. */
	ObjectType heapType();

	/** Returns the memory type. */
	MemoryType memoryType();

	/** Returns the scope type */
	ObjectType scopeType();

	/**
	 * Returns the CIVL-C range type, denoted <code>$range</code>, which
	 * represents a sequence of integers.
	 * 
	 * @return the range type
	 */
	ObjectType rangeType();

	/**
	 * Returns the universal domain type <code>$domain</code>. The domain type
	 * consists of all finite tuples of integers.
	 */
	DomainType domainType();

	/**
	 * Returns the domain type with specified dimension, <code>$domain(n)</code>
	 * . This is a sub-type of <code>$domain</code>, which is the union over all
	 * positive integers <code>n</code> <code>$domain(n)</code>.
	 * 
	 * @param dimension
	 *            the dimension of the domain type, i.e., the arity of the
	 *            tuples in the domain
	 * @return the domain type of the given dimension
	 */
	DomainType domainType(int dimension);

	/************************* Conversions *****************************/

	/**
	 * Computes the type resulting from the "usual arithmetic conversion". From
	 * C11 Sec. 6.3.1.8:
	 * 
	 * <blockquote> Many operators that expect operands of arithmetic type cause
	 * conversions and yield result types in a similar way. The purpose is to
	 * determine a common real type for the operands and result. For the
	 * specified operands, each operand is converted, without change of type
	 * domain, to a type whose corresponding real type is the common real type.
	 * Unless explicitly stated otherwise, the common real type is also the
	 * corresponding real type of the result, whose type domain is the type
	 * domain of the operands if they are the same, and complex otherwise. This
	 * pattern is called the usual arithmetic conversions:
	 * 
	 * <ul>
	 * 
	 * <li>First, if the corresponding real type of either operand is long
	 * double, the other operand is converted, without change of type domain, to
	 * a type whose corresponding real type is long double.</li>
	 * 
	 * <li>Otherwise, if the corresponding real type of either operand is
	 * double, the other operand is converted, without change of type domain, to
	 * a type whose corresponding real type is double.</li>
	 * 
	 * <li>Otherwise, if the corresponding real type of either operand is float,
	 * the other operand is converted, without change of type domain, to a type
	 * whose corresponding real type is float.</li>
	 * 
	 * <li>
	 * Otherwise, the integer promotions are performed on both operands. Then
	 * the following rules are applied to the promoted operands:
	 * 
	 * <ul>
	 * 
	 * <li>If both operands have the same type, then no further conversion is
	 * needed.</li>
	 * 
	 * <li>Otherwise, if both operands have signed integer types or both have
	 * unsigned integer types, the operand with the type of lesser integer
	 * conversion rank is converted to the type of the operand with greater
	 * rank.</li>
	 * 
	 * <li>Otherwise, if the operand that has unsigned integer type has rank
	 * greater or equal to the rank of the type of the other operand, then the
	 * operand with signed integer type is converted to the type of the operand
	 * with unsigned integer type.</li>
	 * 
	 * <li>Otherwise, if the type of the operand with signed integer type can
	 * represent all of the values of the type of the operand with unsigned
	 * integer type, then the operand with unsigned integer type is converted to
	 * the type of the operand with signed integer type.</li>
	 * 
	 * <li>Otherwise, both operands are converted to the unsigned integer type
	 * corresponding to the type of the operand with signed integer type.</li>
	 * 
	 * </ul>
	 * </li> </blockquote>
	 * 
	 * @param type1
	 *            an arithmetic type
	 * @param type2
	 *            an arithmetic type
	 * @return the type of the result of the "usual arithmetic conversion"
	 *         applied to the two types
	 */
	ArithmeticType usualArithmeticConversion(ArithmeticType type1,
			ArithmeticType type2);

	/**
	 * Adds qualifiers and atomic designation as needed to the given type.
	 * 
	 * @param startType
	 *            any object type (qualified or unqualified, atomic or
	 *            non-atomic)
	 * @param atomic
	 *            add atomic qualification to type if not already present?
	 * @param constQualified
	 *            and const qualification to type if not already present?
	 * @param volatileQualified
	 *            add volatile qualification to type if not already present?
	 * @param restrictQualified
	 *            add restrict qualification to type if not already present?
	 * @return type with given qualifications added (none are removed)
	 */
	ObjectType qualify(ObjectType startType, boolean atomic,
			boolean constQualified, boolean volatileQualified,
			boolean restrictQualified, boolean inputQualified,
			boolean outputQualified);

	/**
	 * Is the given type an array-of-char type?
	 * 
	 * @param type
	 * @return
	 */
	boolean isArrayOfCharType(Type type);

	/**
	 * Is the given type a void type?
	 * 
	 * @param type
	 * @return
	 */
	boolean isVoidType(Type type);

	/**
	 * Is the given type a CIVL-C bundle type?
	 * 
	 * @param type
	 * @return
	 */
	boolean isBundleType(Type type);
}
