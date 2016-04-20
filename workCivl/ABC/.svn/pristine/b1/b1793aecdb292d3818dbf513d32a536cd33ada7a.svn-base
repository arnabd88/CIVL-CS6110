package edu.udel.cis.vsl.abc.ast.value.IF;

import java.math.BigInteger;

import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode.Operator;
import edu.udel.cis.vsl.abc.ast.type.IF.ArrayType;
import edu.udel.cis.vsl.abc.ast.type.IF.Field;
import edu.udel.cis.vsl.abc.ast.type.IF.FloatingType;
import edu.udel.cis.vsl.abc.ast.type.IF.IntegerType;
import edu.udel.cis.vsl.abc.ast.type.IF.StructureOrUnionType;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;
import edu.udel.cis.vsl.abc.token.IF.ExecutionCharacter;
import edu.udel.cis.vsl.abc.token.IF.StringLiteral;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;

/**
 * 
 * Constant expressions are discussed in C11 Sec. 6.6:
 * 
 * <blockquote>
 * 
 * A constant expression can be evaluated during translation rather than
 * runtime, and accordingly may be used in any place that a constant may be.
 * 
 * <h2>Constraints</h2>
 * 
 * <ul>
 * <li>3. Constant expressions shall not contain assignment, increment,
 * decrement, function-call, or comma operators, except when they are contained
 * within a subexpression that is not evaluated.(115)</li>
 * <li>4. Each constant expression shall evaluate to a constant that is in the
 * range of representable values for its type.</li>
 * </ul>
 * 
 * <h2>Semantics</h2>
 * 
 * <ul>
 * <li>5. An expression that evaluates to a constant is required in several
 * contexts. If a floating expression is evaluated in the translation
 * environment, the arithmetic range and precision shall be at least as great as
 * if the expression were being evaluated in the execution environment.(116)</li>
 * 
 * <li>6. An integer constant expression(117) shall have integer type and shall
 * only have operands that are integer constants, enumeration constants,
 * character constants, sizeof expressions whose results are integer constants,
 * _Alignof expressions, and floating constants that are the immediate operands
 * of casts. Cast operators in an integer constant expression shall only convert
 * arithmetic types to integer types, except as part of an operand to the sizeof
 * or _Alignof operator.</li>
 * 
 * <li>7. More latitude is permitted for constant expressions in initializers.
 * Such a constant expression shall be, or evaluate to, one of the following:
 * <ul>
 * <li>an arithmetic constant expression,</li>
 * <li>a null pointer constant,</li>
 * <li>an address constant, or</li>
 * <li>an address constant for a complete object type plus or minus an integer
 * constant expression.</li>
 * </ul>
 * </li>
 * 
 * <li>8. An arithmetic constant expression shall have arithmetic type and shall
 * only have operands that are integer constants, floating constants,
 * enumeration constants, character constants, sizeof expressions whose results
 * are integer constants, and _Alignof expressions. Cast operators in an
 * arithmetic constant expression shall only convert arithmetic types to
 * arithmetic types, except as part of an operand to a sizeof or _Alignof
 * operator.</li>
 * 
 * <li>9. An address constant is a null pointer, a pointer to an lvalue
 * designating an object of static storage duration, or a pointer to a function
 * designator; it shall be created explicitly using the unary & operator or an
 * integer constant cast to pointer type, or implicitly by the use of an
 * expression of array or function type. The array-subscript [] and
 * member-access . and -> operators, the address & and indirection * unary
 * operators, and pointer casts may be used in the creation of an address
 * constant, but the value of an object shall not be accessed by use of these
 * operators.</li>
 * 
 * <li>10. An implementation may accept other forms of constant expressions.</li>
 * 
 * <li>11. The semantic rules for the evaluation of a constant expression are
 * the same as for nonconstant expressions.</li>
 * </ul>
 * </blockquote>
 * 
 * Footnotes:
 * 
 * <blockquote>
 * <ul>
 * <li>115) The operand of a sizeof or _Alignof operator is usually not
 * evaluated (6.5.3.4).</li>
 * <li>116) The use of evaluation formats as characterized by FLT_EVAL_METHOD
 * also applies to evaluation in the translation environment.</li>
 * <li>117) An integer constant expression is required in a number of contexts
 * such as the size of a bit-field member of a structure, the value of an
 * enumeration constant, and the size of a non-variable length array. Further
 * constraints that apply to the integer constant expressions used in
 * conditional-inclusion preprocessing directives are discussed in 6.10.1.</li>
 * </ul>
 * </blockquote>
 * 
 * In addition, string literals and compound literals.
 * 
 * @author siegel
 * 
 */
public interface ValueFactory {

	public enum Answer {
		YES, NO, MAYBE;
	}

	/**
	 * Evaluates a constant expression.
	 * 
	 * @param constantExpression
	 *            a constant expression
	 * @return value of that expression
	 * @throws SyntaxException
	 *             if expression is not a constant expression
	 */
	Value evaluate(ExpressionNode constantExpression) throws SyntaxException;

	/**
	 * Is the value a zero value? Maybe, maybe not: how to deal? Thm prover
	 * time.
	 * 
	 * @param value
	 *            a value
	 * @return yes, no, or maybe, depending on whether the value is determined
	 *         to be zero
	 */
	Answer isZero(Value value);

	// Value creation...

	IntegerValue plusOne(IntegerValue value);

	CharacterValue characterValue(ExecutionCharacter character);

	StringValue stringValue(StringLiteral literal);

	IntegerValue integerValue(IntegerType type, BigInteger integerValue);

	/**
	 * An integer value of the given type and with the given Java int value.
	 * Provided for convenience.
	 * 
	 * @param type
	 *            an integer type
	 * @param intValue
	 *            a Java int
	 * @return the integer value with given type and int value
	 */
	IntegerValue integerValue(IntegerType type, int intValue);

	RealFloatingValue realFloatingValue(FloatingType type, int radix,
			BigInteger wholePartValue, BigInteger fractionPartValue,
			int fractionLength, BigInteger exponentValue);

	ComplexValue complexValue(FloatingType type, RealFloatingValue realPart,
			RealFloatingValue imaginaryPart);

	Value sizeofValue(Type type);

	TypeValue alignofValue(Type type);

	CastValue castValue(Type castType, Value argument);

	AddressValue addressValue(ExpressionNode lhs) throws SyntaxException;

	/**
	 * The legal operators are:
	 * 
	 * <ul>
	 * <li>ADDRESSOF: & pointer to object</li>
	 * <li>BITAND: & bit-wise and</li>
	 * <li>BITCOMPLEMENT: ~ bit-wise complement</li>
	 * <li>BITOR: | bit-wise inclusive or</li>
	 * <li>BITXOR: ^ bit-wise exclusive or</li>
	 * <li>CONDITIONAL: ?: the conditional operator</li>
	 * <li>DEREFERENCE: * pointer dereference</li>
	 * <li>DIV: / numerical division</li>
	 * <li>EQUALS: == equality</li>
	 * <li>GT: > greater than</li>
	 * <li>GTE: >= greater than or equals</li>
	 * <li>LAND: && logical and</li>
	 * <li>LOR: || logical or</li>
	 * <li>LT: < less than</li>
	 * <li>LTE: <= less than or equals</li>
	 * <li>MINUS: - binary subtraction (numbers and pointers)</li>
	 * <li>MOD: % integer modulus</li>
	 * <li>NEQ: != not equals</li>
	 * <li>NOT: ! logical not</li>
	 * <li>PLUS: + binary addition, numeric or pointer</li>
	 * <li>SHIFTLEFT: << shift left</li>
	 * <li>SHIFTRIGHT: >> shift right</li>
	 * <li>SUBSCRIPT: [] array subscript</li>
	 * <li>TIMES: * numeric multiplication</li>
	 * <li>UNARYMINUS: - numeric negative</li>
	 * <li>UNARYPLUS // + numeric no-op</li>
	 * </ul>
	 * 
	 * @param operator
	 *            one of the legal value operators
	 * @param arguments
	 *            list of arguments to that operator
	 * @return an OperatorValue as specified
	 */
	OperatorValue operatorValue(Type type, Operator operator, Value[] arguments);

	/**
	 * Creates a new empty array value. The value can be completed using the
	 * methods provided in ArrayValue.
	 */
	ArrayValue newArrayValue(ArrayType type);

	StructureValue newStructureValue(StructureOrUnionType type);

	UnionValue newUnionValue(StructureOrUnionType unionType, Field field,
			Value memberValue);

}
