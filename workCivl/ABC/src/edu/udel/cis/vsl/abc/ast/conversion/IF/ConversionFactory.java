package edu.udel.cis.vsl.abc.ast.conversion.IF;

import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.type.IF.ArithmeticType;
import edu.udel.cis.vsl.abc.ast.type.IF.ArrayType;
import edu.udel.cis.vsl.abc.ast.type.IF.DomainType;
import edu.udel.cis.vsl.abc.ast.type.IF.FunctionType;
import edu.udel.cis.vsl.abc.ast.type.IF.IntegerType;
import edu.udel.cis.vsl.abc.ast.type.IF.ObjectType;
import edu.udel.cis.vsl.abc.ast.type.IF.PointerType;
import edu.udel.cis.vsl.abc.ast.type.IF.StructureOrUnionType;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;
import edu.udel.cis.vsl.abc.ast.type.IF.TypeFactory;
import edu.udel.cis.vsl.abc.ast.type.IF.UnqualifiedObjectType;
import edu.udel.cis.vsl.abc.config.IF.Configuration;
import edu.udel.cis.vsl.abc.token.IF.UnsourcedException;

/**
 * A factory for producing instances of {@link Conversion}.
 * 
 * @author siegel
 * 
 */
public interface ConversionFactory {

	TypeFactory getTypeFactory();

	/**
	 * Returns an ArithmeticConversion object with given old type and new type.
	 * Note that the newType is determined by applying an algorithm to two
	 * types, of which the old type is one. The usual way to use these methods
	 * when given two arithmetic types type1 and type2 is as follows: let
	 * newType = usualArithmeticConversion(type1, type2). If newType != type1,
	 * let c1 = arithmeticConversion(type1, newType) and add the nontrivial
	 * conversion c1 to the sequence of conversions for its expression. Repeat
	 * for type2: if newType != type2, let c2=arithmeticConversion(type2,
	 * newType) and add c2 to the sequence of conversions for its expression.
	 * 
	 * @param oldType
	 *            an arithmetic type: the original type of an expression
	 * @param newType
	 *            the arithmetic type that results after applying a usual
	 *            arithmetic conversion
	 * @return an object representing the conversion of the old type to the new
	 */
	ArithmeticConversion arithmeticConversion(ArithmeticType oldType,
			ArithmeticType newType);

	/**
	 * Returns a non-trivial {@link LvalueConversion} with old type the given
	 * type, or null if the conversion is trivial.
	 * 
	 * C11 Sec. 6.3.2.1:
	 * 
	 * <blockquote>
	 * 
	 * Except when it is the operand of the sizeof operator, the
	 * <code>_Alignof</code> operator, the unary <code>&</code> operator, the
	 * <code>++</code> operator, the <code>--</code> operator, or the left
	 * operand of the <code>.</code> operator or an assignment operator, an
	 * lvalue that does not have array type is converted to the value stored in
	 * the designated object (and is no longer an lvalue); this is called lvalue
	 * conversion. If the lvalue has qualified type, the value has the
	 * unqualified version of the type of the lvalue; additionally, if the
	 * lvalue has atomic type, the value has the non-atomic version of the type
	 * of the lvalue; otherwise, the value has the type of the lvalue. If the
	 * lvalue has an incomplete type and does not have array type, the behavior
	 * is undefined. If the lvalue designates an object of automatic storage
	 * duration that could have been declared with the register storage class
	 * (never had its address taken), and that object is uninitialized (not
	 * declared with an initializer and no assignment to it has been performed
	 * prior to use), the behavior is undefined.
	 * 
	 * </blockquote>
	 * 
	 * @param type
	 *            an object type
	 * @return either (1) an LvalueConversion with old type the given ObjectType
	 *         and new type determined as follows: if qualified, the unqualified
	 *         version; if atomic, the non-atomic version; or (2) null if the
	 *         conversion is trivial (new type same as old)
	 */
	LvalueConversion lvalueConversion(ObjectType type);

	/**
	 * Returns the type that would result from applying lvalue conversion to the
	 * given type.
	 * 
	 * @param type
	 *            any object type
	 * @return result of lvalue conversion
	 */
	UnqualifiedObjectType lvalueConversionType(ObjectType type);

	/**
	 * Returns the array conversion with old type the given type.
	 * 
	 * C11 Sec. 6.3.2.1:
	 * 
	 * "Except when it is the operand of the <code>sizeof</code> operator, the
	 * <code>_Alignof</code> operator, or the unary <code>&</code> operator, or
	 * is a string literal used to initialize an array, an expression that has
	 * type "array of type" is converted to an expression with type
	 * "pointer to type" that points to the initial element of the array object
	 * and is not an lvalue. If the array object has register storage class, the
	 * behavior is undefined."
	 * 
	 * @param type
	 *            any array type
	 * @return array conversion with old type the given array type and new type
	 *         the pointer type to the element type of the array type
	 */
	ArrayConversion arrayConversion(ArrayType type);

	/**
	 * Returns the function conversion object with old type equal to the given
	 * function type.
	 * 
	 * C11 Sec. 6.3.2.1:
	 * 
	 * <blockquote> A function designator is an expression that has function
	 * type. Except when it is the operand of the <code>sizeof</code> operator,
	 * the <code>_Alignof</code> operator, or the unary <code>&</code> operator,
	 * a function designator with type "function returning type" is converted to
	 * an expression that has type "pointer to function returning type".
	 * </blockquote>
	 * 
	 * @param type
	 *            a function type
	 * @return a FunctionConversion with old type the given function type and
	 *         new type the pointer type to the function type
	 */
	FunctionConversion functionConversion(FunctionType type);

	/**
	 * Creates a new compatible-structure-or-union-conversion object from the
	 * given structure-or-union types.
	 * 
	 * @param type1
	 *            a structure or union type
	 * @param type2
	 *            a compatible structure or union type
	 * @return the conversion from type1 to type2
	 */
	CompatibleStructureOrUnionConversion compatibleStructureOrUnionConversion(
			StructureOrUnionType type1, StructureOrUnionType type2);

	/**
	 * Creates a new compatible-pointer-conversion object from the first pointer
	 * type to the second.
	 * 
	 * @param type1
	 *            a pointer type
	 * @param type2
	 *            a pointer type which is either compatible with type1 or is
	 *            obtained from type1 by adding qualifiers to the type of thing
	 *            pointed to
	 * @return the conversion
	 */
	CompatiblePointerConversion compatiblePointerConversion(PointerType type1,
			PointerType type2);

	/**
	 * <p>
	 * Creates a new conversion object between some pointer type and the type
	 * <code>void*</code> (pointer-to-void). From C11 Sec. 6.3.2.3:
	 * 
	 * <blockquote> A pointer to void may be converted to or from a pointer to
	 * any object type. A pointer to any object type may be converted to a
	 * pointer to void and back again; the result shall compare equal to the
	 * original pointer. </blockquote>
	 * </p>
	 * 
	 * <p>
	 * One of the two arguments must be a pointer-to-void.
	 * </p>
	 * 
	 * @param type1
	 *            a pointer type
	 * @param type2
	 *            a pointer type
	 * @return the conversion object from type1 to type2
	 */
	VoidPointerConversion voidPointerConversion(PointerType type1,
			PointerType type2);

	/**
	 * Conversion from an integer constant with value 0 or such cast to a void*,
	 * to a pointer type.
	 * 
	 * @param type1
	 *            an integer type or pointer-to-void
	 * @param type2
	 *            any pointer type
	 * @return conversion from type1 to type2
	 */
	NullPointerConversion nullPointerConversion(ObjectType type1,
			PointerType type2);

	/**
	 * Conversion from any pointer type to a boolean (<code>_Bool</code>).
	 * 
	 * @param oldType
	 * @return PointerBoolConversion with given oldType and newType the boolean
	 *         type
	 */
	PointerBoolConversion pointerBoolConversion(PointerType oldType);

	/**
	 * Given (1) the processed right hand side of an assignment expression and
	 * (2) the type of the assignment expression (i.e., the adjusted type of the
	 * left hand side), returns the conversion from the right-hand type to the
	 * assignment type. If no conversion is necessary because the types are
	 * equal, returns null. If no such conversion exists, an exception is
	 * thrown.
	 * 
	 * C11 Section 6.5.16(3) states:
	 * 
	 * <blockquote> An assignment operator stores a value in the object
	 * designated by the left operand. An assignment expression has the value of
	 * the left operand after the assignment,111) but is not an lvalue. The type
	 * of an assignment expression is the type the left operand would have after
	 * lvalue conversion. The side effect of updating the stored value of the
	 * left operand is sequenced after the value computations of the left and
	 * right operands. The evaluations of the operands are unsequenced.
	 * </blockquote>
	 * 
	 * and C11 Section 6.5.16.1 continues:
	 * 
	 * <blockquote> One of the following shall hold:
	 * 
	 * <ul>
	 * <li>the left operand has atomic, qualified, or unqualified arithmetic
	 * type, and the right has arithmetic type;</li>
	 * 
	 * <li>the left operand has an atomic, qualified, or unqualified version of
	 * a structure or union type compatible with the type of the right;</li>
	 * 
	 * <li>the left operand has atomic, qualified, or unqualified pointer type,
	 * and (considering the type the left operand would have after lvalue
	 * conversion) both operands are pointers to qualified or unqualified
	 * versions of compatible types, and the type pointed to by the left has all
	 * the qualifiers of the type pointed to by the right;</li>
	 * 
	 * <li>the left operand has atomic, qualified, or unqualified pointer type,
	 * and (considering the type the left operand would have after lvalue
	 * conversion) one operand is a pointer to an object type, and the other is
	 * a pointer to a qualified or unqualified version of void, and the type
	 * pointed to by the left has all the qualifiers of the type pointed to by
	 * the right;</li>
	 * 
	 * <li>the left operand is an atomic, qualified, or unqualified pointer, and
	 * the right is a null pointer constant; or</li>
	 * 
	 * <li>the left operand has type atomic, qualified, or unqualified _Bool,
	 * and the right is a pointer.</li>
	 * </ul>
	 * </blockquote>
	 * 
	 * These suggest the following types of conversions be used, respectively,
	 * for the cases above: {@link ArithmeticConversion},
	 * {@link CompatibleStructureOrUnionConversion},
	 * {@link CompatiblePointerConversion}, {@link VoidPointerConversion},
	 * {@link NullPointerConversion}, {@link PointerBoolConversion}.
	 * 
	 * The processing of a simple assignement expression then proceeds as
	 * follows:
	 * 
	 * <ol>
	 * <li>let <code>newType</code> be the result of applying lvalue conversion
	 * to the lhs expression and make this the initial type of the assignment
	 * expression</li>
	 * <li>add standard conversions to rhs expression and call the resulting
	 * type <code>oldType</code></li>
	 * <li>consider cases above to generate a conversion from
	 * <code>oldType</code> to <code>newType</code>; add that conversion to rhs
	 * expression</li>
	 * </ol>
	 * 
	 * This method helps in the above process by finding the right conversion
	 * for the last step.
	 * 
	 * 
	 * @param rhs
	 *            the right-hand side of the assignment, after having been
	 *            processed and the standard conversions applied
	 * @param newType
	 *            the type of the assignment expression, i.e., the type to which
	 *            the rhs expression must be converted; it is the result of
	 *            applying lvalue conversion to the left hand side.
	 * @throws UnsourcedException
	 */
	Conversion assignmentConversion(Configuration config, ExpressionNode rhs,
			Type newType) throws UnsourcedException;

	/**
	 * When a range expression is used in $for or $parfor, it is converted
	 * automatically to $domain type.
	 * 
	 * @param rangeType
	 * @param domainType
	 * @return
	 */
	RegularRangeToDomainConversion regularRangeToDomainConversion(
			ObjectType rangeType, DomainType domainType);

	/**
	 * Is this expression a null pointer constant? Prerequisite: node has
	 * already been processed.
	 * 
	 * A null pointer constant is either (1) an integer constant with value 0,
	 * or (2) such a constant cast to (void *).
	 * 
	 * @param node
	 *            an expression node
	 * @return true iff expression is a null pointer constant, else false
	 */
	boolean isNullPointerConstant(ExpressionNode node);

	/**
	 * Is the given pointer type a pointer to a qualified or unqualified version
	 * of void?
	 * 
	 * @param type
	 *            any (unqualified) pointer type
	 * @return true iff the referenced type is a qualified (including atomic) or
	 *         unqualified version of void
	 */
	boolean isPointerToVoid(PointerType type);

	/**
	 * Is the given pointer type a pointer an object type?
	 * 
	 * @param type
	 * @return <code>true</code> iff the pointer type's base type is an object
	 *         type
	 */
	boolean isPointerToObject(PointerType type);

	/**
	 * Returns the memory conversion with old type the given type.
	 *
	 * @param type
	 *            any object type
	 * @return memory conversion with old type being the given type and new type
	 *         the memory type
	 */
	MemoryConversion memoryConversion(Type type);

	/**
	 * creates a pointer-to-integer type conversion
	 * 
	 * @param oldType
	 * @param newType
	 * @return
	 */
	Pointer2IntegerConversion pointer2IntegerConversion(PointerType oldType,
			IntegerType newType);

	/**
	 * creates a integer-to-pointer type conversion
	 * 
	 * @param oldType
	 * @param newType
	 * @return
	 */
	Integer2PointerConversion integer2PointerConversion(IntegerType oldType,
			PointerType newType);

}
