package edu.udel.cis.vsl.sarl.IF;

import java.io.PrintStream;
import java.math.BigInteger;
import java.util.Collection;
import java.util.Comparator;
import java.util.Map;
import java.util.Set;

import edu.udel.cis.vsl.sarl.IF.expr.ArrayElementReference;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.OffsetReference;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.expr.TupleComponentReference;
import edu.udel.cis.vsl.sarl.IF.expr.UnionMemberReference;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.number.Number;
import edu.udel.cis.vsl.sarl.IF.number.NumberFactory;
import edu.udel.cis.vsl.sarl.IF.number.RationalNumber;
import edu.udel.cis.vsl.sarl.IF.object.BooleanObject;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;
import edu.udel.cis.vsl.sarl.IF.object.NumberObject;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicCompleteArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicFunctionType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicIntegerType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicMapType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicRealType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicSetType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicUnionType;
import edu.udel.cis.vsl.sarl.util.Pair;

/**
 * A {@link CoreUniverse} provides most of the functionality of a
 * {@link SymbolicUniverse}, including the mechanisms to create and manipulate
 * {@link SymbolicExpression}s and other {@link SymbolicObject}s. The part that
 * is missing deals with "reasoning", i.e., the ability to determine the
 * validity of formulas and to simplify expressions within a "context".
 * 
 * @author siegel
 */
public interface CoreUniverse {

	// General...

	/**
	 * Gets the <code>showQueries</code> flag: if <code>true</code>, SARL
	 * theorem prover queries will be printed to the output stream.
	 * 
	 * @return current value of the <code>showQueries</code> flag
	 * @see #setShowQueries(boolean)
	 * @see #getShowProverQueries()
	 * @see #setShowProverQueries(boolean)
	 */
	boolean getShowQueries();

	/**
	 * Sets the <code>showQueries</code> flag. If this is set to
	 * <code>true</code>, SARL theorem prover queries will be printed to the
	 * output stream.
	 * 
	 * @param value
	 *            new value for the <code>showQueries</code> flag.
	 * @see #getShowQueries()
	 * @see #getShowProverQueries()
	 * @see #setShowProverQueries(boolean)
	 */
	void setShowQueries(boolean value);

	/**
	 * Gets the <code>showProverQueries</code> flag: if <code>true</code>, the
	 * theorem prover queries processed by the underlying theorem prover(s) will
	 * be printed to the output stream.
	 * 
	 * @return current value of the <code>showProverQueries</code> flag
	 * @see #setShowProverQueries(boolean)
	 * @see #getShowQueries()
	 * @see #setShowQueries(boolean)
	 */
	boolean getShowProverQueries();

	/**
	 * Sets the <code>showProverQueries</code> flag. If set to <code>true</code>
	 * , the theorem prover queries processed by the underlying theorem
	 * prover(s) will be printed to the output stream.
	 * 
	 * @param value
	 *            new value for the <code>showProverQueries</code> flag
	 * @see #getShowProverQueries()
	 * @see #getShowQueries()
	 * @see #setShowQueries(boolean)
	 */
	void setShowProverQueries(boolean value);

	/**
	 * Returns the output stream to which information (such as queries) will be
	 * printed. By default, standard out.
	 * 
	 * @return current output stream
	 * @see #setOutputStream(PrintStream)
	 */
	PrintStream getOutputStream();

	/**
	 * Sets the output stream, the stream to which information (such as queries)
	 * will be printed. By default, standard out.
	 * 
	 * @param out
	 *            new value for output stream
	 * @see #getOutputStream()
	 */
	void setOutputStream(PrintStream out);

	/**
	 * Returns a comparator on the set of all symbolic objects. This defines a
	 * total order on all symbolic objects.
	 * 
	 * @return a comparator on all symbolic objects
	 */
	Comparator<SymbolicObject> comparator();

	/**
	 * <p>
	 * Returns the unique representative instance from the given object's
	 * equivalence class, where the equivalence relation is determined by the
	 * "equals" method. (Refer to the "Flyweight Pattern".)
	 * </p>
	 * 
	 * <p>
	 * A symbolic universe does not necessarily use the Flyweight Pattern on the
	 * symbolic objects it creates, but this method gives the user the option to
	 * use that pattern, in full or in part.
	 * </p>
	 * 
	 * <p>
	 * The methods in this universe which return symbolic expressions may return
	 * distinct instances which are equivalent (under "equals"). However,
	 * canonic is guaranteed to return a unique instance from each equivalence
	 * class, i.e., if <code>a.equals(b)</code> then
	 * <code>canonic(a)==canonic(b)</code>.
	 * </p>
	 * 
	 * @param object
	 *            a symbolic object
	 * @return canonical representative equal to <code>object</code>
	 * @see #canonic(SymbolicExpression)
	 */
	SymbolicObject canonic(SymbolicObject object);

	/**
	 * <p>
	 * Returns the unique representative instance from the given expression's
	 * equivalence class, where the equivalence relation is determined by the
	 * "equals" method.
	 * </p>
	 * 
	 * <p>
	 * The result is the same as that of {@link #canonic(SymbolicObject)}, but
	 * since the result of {@link #canonic(SymbolicObject)} on a
	 * {@link SymbolicExpression} must be a {@link SymbolicExpression}, this
	 * method is provided so that callers don't have to cast.
	 * </p>
	 * 
	 * @param expression
	 *            any {@link SymbolicExpression} belonging to this universe
	 * @return the canonic representative equal to <code>expression</code>
	 * @see #canonic(SymbolicObject)
	 */
	SymbolicExpression canonic(SymbolicExpression expression);

	/**
	 * Returns the number of canonic symbolic objects controlled by this
	 * universe.
	 * 
	 * @return the number of canonic symbolic objects
	 */
	int numObjects();

	/**
	 * <p>
	 * Gets the canonic {@link SymbolicObject} belonging to this universe with
	 * the given ID number.
	 * </p>
	 * 
	 * <p>
	 * Each canonic symbolic object is assigned a unique ID number. The numbers
	 * start from 0 and there are no gaps, i.e., they are in the range
	 * 0..numExpressions-1.
	 * </p>
	 * 
	 * @param id
	 *            the ID number of a {@link SymbolicObject} belonging to this
	 *            universe
	 * 
	 * @return the canonic symbolic object with the given ID number.
	 */
	SymbolicObject objectWithId(int id);

	/**
	 * Returns the set of all canonic {@link SymbolicObject}s controlled by this
	 * universe as a Java {@link Collection}.
	 * 
	 * @return the set of all canonic symbolic objects
	 */
	Collection<SymbolicObject> objects();

	// Types...

	/**
	 * Returns a boolean expression which holds iff the two types are
	 * compatible. Two types are compatible if it is possible for them to have a
	 * value in common. For the most part, this is the same as saying they are
	 * the same type. The exception is that an incomplete
	 * {@link SymbolicArrayType} and a {@link SymbolicCompleteArrayType} with
	 * compatible element types are compatible.
	 * 
	 * @param type0
	 *            a non-<code>null</code> symbolic type
	 * @param type1
	 *            a non-<code>null</code> symbolic type
	 * @return a boolean expression which holds iff the two types are compatible
	 * 
	 * @see #pureType(SymbolicType)
	 */
	BooleanExpression compatible(SymbolicType type0, SymbolicType type1);

	/**
	 * Returns the "pure" version of the type, i.e., the compatible
	 * {@link SymbolicType} that contains no {@link SymbolicExpression}s. It is
	 * obtained by making every array type incomplete, i.e., by removing the
	 * length expressions from complete array types. This is applied recursively
	 * down all components of the type tree.
	 * 
	 * @see #compatible(SymbolicType, SymbolicType)
	 */
	SymbolicType pureType(SymbolicType type);

	/**
	 * The boolean type.
	 * 
	 * @return the boolean type
	 */
	SymbolicType booleanType();

	/**
	 * The "ideal" integer type, representing the set of mathematical integers.
	 * 
	 * @return the integer type
	 * @see #herbrandIntegerType()
	 * @see #boundedIntegerType(NumericExpression, NumericExpression, boolean)
	 */
	SymbolicIntegerType integerType();

	/**
	 * <p>
	 * Returns the Herbrand integer type. All operations in which at least one
	 * argument has Herbrand integer type will be treated as uninterpreted
	 * functions: no simplifications or other transformations will be performed.
	 * </p>
	 * 
	 * <p>
	 * Note: to create a concrete number of Herbrand integer type, create an
	 * ideal concrete integer then cast it to the Herbrand type.
	 * </p>
	 * 
	 * @return the Herbrand integer type
	 * @see #integerType()
	 * @see #boundedIntegerType(NumericExpression, NumericExpression, boolean)
	 */
	SymbolicIntegerType herbrandIntegerType();

	/**
	 * <p>
	 * Returns the bounded integer types with specified upper and lower bounds.
	 * Either of the bounds may be <code>null</code>, indicating there is no
	 * bound (i.e., the bound is + or - infinity). If <code>cyclic</code> is
	 * <code>true</code>, then all operations treat the domain cyclically (i.e.,
	 * max+1 = min).
	 * </p>
	 * 
	 * <p>
	 * <strong>NOTE: THIS IS NOT YET IMPLEMENTED.</strong>
	 * </p>
	 * 
	 * @param min
	 *            smallest integer value in the domain or <code>null</code>
	 * @param max
	 *            largest integer value in the domain or <code>null</code>
	 * @param cyclic
	 *            should operations treat the domain cyclically?
	 * @return the bounded integer type as specified
	 * 
	 * @see #integerType()
	 * @see #herbrandIntegerType()
	 */
	SymbolicIntegerType boundedIntegerType(NumericExpression min,
			NumericExpression max, boolean cyclic);

	/**
	 * The "ideal" real type, representing the set of mathematical real numbers.
	 * 
	 * @return the real type
	 * @see #herbrandRealType()
	 */
	SymbolicRealType realType();

	/**
	 * <p>
	 * Returns the Herbrand real type. All operations in which at least one
	 * argument has Herbrand real type will be treated as uninterpreted
	 * functions: no simplifications or other transformations will be performed.
	 * Operations may involve mixed real and Herbrand real types, but the result
	 * will always be a Herbrand expression as long as at least one argument is
	 * Herbrand.
	 * </p>
	 * 
	 * <p>
	 * A Herbrand value and non-Herbrand value are always considered to be not
	 * equal, even if they are concrete expressions.
	 * </p>
	 * 
	 * <p>
	 * Note: to create a concrete number of herbrand real type, create an ideal
	 * concrete real then cast it to the herbrand type.
	 * </p>
	 * 
	 * @return the Herbrand real type
	 * @see #realType()
	 */
	SymbolicRealType herbrandRealType();

	// TODO: floating point types

	/**
	 * Returns the character type.
	 * 
	 * @return the character type
	 */
	SymbolicType characterType();

	/**
	 * Returns the complete array type with the given element type and extent
	 * (array length). Neither argument can be <code>null</code>.
	 * 
	 * @param elementType
	 *            the type of the elements of the array
	 * @param the
	 *            length of the array
	 * 
	 * @return the complete array type as specified
	 * @see #arrayType(SymbolicType)
	 */
	SymbolicCompleteArrayType arrayType(SymbolicType elementType,
			NumericExpression extent);

	/**
	 * Returns the incomplete array type with the given element type. The
	 * element type cannot be <code>null</code>.
	 * 
	 * @return the incomplete array type
	 * @see #arrayType(SymbolicType, NumericExpression)
	 */
	SymbolicArrayType arrayType(SymbolicType elementType);

	/**
	 * <p>
	 * Returns the dimension and base type of an array type.
	 * </p>
	 * 
	 * <p>
	 * The dimension and base type of an array type <i>T</i>[] are defined as
	 * follows: if <i>T</i> is an array type, the dimension of <i>T</i>[] is one
	 * plus the dimension of <i>T</i>, and the base type of <i>T</i>[] is the
	 * base type of <i>T</i> . Otherwise, the dimension of <i>T</i>[] is 1 and
	 * the base type is <i>T</i>.
	 * </p>
	 * 
	 * @param type
	 *            a non-<code>null</code> array type
	 * @return A {@link Pair} consisting of dimension (left) and base type
	 *         (right).
	 */
	Pair<Integer, SymbolicType> arrayDimensionAndBaseType(SymbolicArrayType type);

	/**
	 * Returns the tuple type defined by the given sequence of component types.
	 * The tuple type consists of all tuples of values (<i>x</i><sub>0</sub>,
	 * ..., <i>x</i><sub>n-1</sub>), where <i>x</i><sub><i>i</i></sub> has type
	 * <code>fieldsTypes</code><sub><i>i</i></sub>. A tuple type also has a
	 * name, and two tuple types are not equal if they have unequal names.
	 * 
	 * @param name
	 *            the name of the tuple type
	 * @param fieldTypes
	 *            an iterable object specifying the sequence of component types
	 *            for the tuple type
	 * 
	 * @return the tuple type specified by the given name and field types
	 */
	SymbolicTupleType tupleType(StringObject name,
			Iterable<? extends SymbolicType> fieldTypes);

	/**
	 * Returns the specified function type. A function type is specified by a
	 * sequence of input types, and an output type.
	 * 
	 * @param inputTypes
	 *            sequence of input types
	 * @param outputType
	 *            the output type of the function
	 * @return the function type
	 */
	SymbolicFunctionType functionType(
			Iterable<? extends SymbolicType> inputTypes, SymbolicType outputType);

	// 	@formatter:off

	/**
	 * <p>
	 * Returns the type which is the union of the given member types.
	 * </p>
	 * 
	 * <p>
	 * Say the member types are <i>t</i><sub>0</sub>,...,<i>t</i><sub>n-1</sub> and call
	 * the union type <i>u</i>. For 0 &le; <i>i</i> &lt; <i>n</i>, there are
	 * functions inject<sub>i</sub>: <i>t</i><sub><i>i</i></sub> &rarr; <i>u</i>,
	 * extract<sub><i>i</i></sub>: <i>u</i> &rarr; <i>t</i><sub><i>i</i></sub>,
	 * and
	 * test<sub><i>i</i></sub>: <i>u</i>  &rarr; {<i>true</i>,<i>false</i>}.
	 * The domain of <i>u</i> consists of all expressions of the form 
	 * inject<sub><i>i</i></sub>(<i>x<sub>i</sub></i>).
	 * </p>
	 * 
	 * <p>
	 * We have
	 * extract<sub><i>i</i></sub>(inject<sub><i>i</i></sub>(<i>x</i>))=<i>x</i>
	 * and extract<sub><i>i</i></sub> is undefined on any element of
	 * <i>u</i> that is not in the image of inject<sub><i>i</i></sub>.
	 * test<sub><i>i</i></sub>(<i>x</i>) is <i>true</i> iff
	 * x=inject<sub><i>i</i></sub>(<i>x<sub>i</sub></i>)
	 * for some <i>x<sub>i</sub></i> in <i>t<sub>i</sub></i>.
	 * </p>
	 * 
	 * @param name
	 *            the name of the union type
	 * @param memberTypes
	 *            the sequence of member types
	 * @return the specified union type
	 */
	SymbolicUnionType unionType(StringObject name,
			Iterable<? extends SymbolicType> memberTypes);
	
	// @formatter:on

	/**
	 * Returns the type for "set of T"; not yet implemented.
	 * 
	 * @param elementType
	 *            type of elements of the set
	 * @return the type "set of <code>elementType</code>"
	 */
	SymbolicSetType setType(SymbolicType elementType);

	/**
	 * Under construction.
	 * 
	 * @param keyType
	 * @param valueType
	 * @return
	 */
	SymbolicMapType mapType(SymbolicType keyType, SymbolicType valueType);

	/**
	 * Returns a tuple type which has two components: component 0 is the key
	 * type of the map type; component 1 is the value type of the map type. This
	 * is the type of an "entry" in the map. This type is used by the method
	 * {@link #entrySet(SymbolicExpression)}, which returns the set of entries
	 * of a map.
	 * 
	 * @param mapType
	 *            a map type
	 * @return the type of an entry in the map
	 */
	SymbolicTupleType entryType(SymbolicMapType mapType);

	// Other...

	/**
	 * Returns a substituter for which the base substitutions are specified by
	 * an explicit Java {@link Map}. The map specifies a set of key-value pairs.
	 * The substituter will replace any key with its corresponding value; all
	 * other substitutions are determined from those "base" cases by recursive
	 * application of substitution.
	 * 
	 * @param map
	 *            a map which specifies that a key should be replaced by the
	 *            corresponding value
	 * @return a substituter based on the given map
	 */
	UnaryOperator<SymbolicExpression> mapSubstituter(
			Map<SymbolicExpression, SymbolicExpression> map);

	/**
	 * Returns a substituter specified by a mapping of old names to new names
	 * for symbolic constants. Any symbolic constant appearing as a key in the
	 * map will be replaced by a similar one with name the corresponding value.
	 * This includes bound symbolic constants.
	 * 
	 * @param nameMap
	 *            mapping of old to new names for symbolic constants
	 * @return a substituter which replaces symbolic constants as specified by
	 *         <code>nameMap</code>
	 */
	UnaryOperator<SymbolicExpression> nameSubstituter(
			Map<StringObject, StringObject> nameMap);

	/**
	 * Returns a substituter that replaces a specific symbolic constant with
	 * some specific value. The value must have a type that is compatible with
	 * that of the symbolic constant.
	 * 
	 * @param var
	 *            the symbolic constant
	 * @param value
	 *            the value that will replace the symbolic constant
	 * @return a substituter that will replace any occurrence of
	 *         <code>var</code> with <code>value</code>
	 */
	UnaryOperator<SymbolicExpression> simpleSubstituter(SymbolicConstant var,
			SymbolicExpression value);

	/**
	 * <p>
	 * Returns an operator on {@link SymbolicExpression}s that replaces all
	 * symbolic constants (including bound ones) with symbolic constants with
	 * unique canonical names. The names are formed by appending the integers 0,
	 * 1, ..., to <code>root</code>. The renamer has state, so it can be used
	 * repeatedly (applied to multiple symbolic expressions) and will continue
	 * to generate new names for the new symbolic constants it encounters if
	 * they have not been encountered before. Every fresh binding of a bound
	 * variable is considered to be new, so is given a unique new name.
	 * </p>
	 * 
	 * <p>
	 * The parameter <code>ignore</code> also provides a way to specify that
	 * certain symbolic constants should be ignored, i.e., they should not be
	 * renamed.
	 * </p>
	 * 
	 * @param root
	 *            the string that forms the root of the names of the new
	 *            symbolic constants
	 * @param ignore
	 *            a predicate providing a method that takes a
	 *            {@link SymbolicConstant} and returns <code>true</code> or
	 *            <code>false</code>; if it returns <code>true</code>, then that
	 *            symbolic constant should <strong>not</strong> be renamed
	 * @return a unary operator which take a symbolic expression and returns a
	 *         symbolic expression in which the symbolic constants have been
	 *         assigned canonical names
	 */
	UnaryOperator<SymbolicExpression> canonicalRenamer(String root,
			Predicate<SymbolicConstant> ignore);

	/**
	 * <p>
	 * Returns an operator on {@link SymbolicExpression}s that replaces all
	 * symbolic constants (including bound ones) with symbolic constants with
	 * unique canonical names. The names are formed by appending the integers 0,
	 * 1, ..., to <code>root</code>. The renamer has state, so it can be used
	 * repeatedly (applied to multiple symbolic expressions) and will continue
	 * to generate new names for the new symbolic constants it encounters if
	 * they have not been encountered before. Every fresh binding of a bound
	 * variable is considered to be new, so is given a unique new name.
	 * </p>
	 * 
	 * <p>
	 * Equivalent to invoking {@link #canonicalRenamer(String, Predicate)} with
	 * <code>ignore</code> the constant predicate <code>false</code>.
	 * </p>
	 * 
	 * @param root
	 *            the string that forms the root of the names of the new
	 *            symbolic constants
	 * @return a unary operator which take a symbolic expression and returns a
	 *         symbolic expression in which the symbolic constants have been
	 *         assigned canonical names
	 */
	UnaryOperator<SymbolicExpression> canonicalRenamer(String root);

	/**
	 * Applies the given operator to the arguments and returns the resulting
	 * expression in the form used by this universe. The arguments should have
	 * the form required by the operator; see the documentation in the
	 * {@link SymbolicExpression} interface, especially for the
	 * {@link SymbolicOperator}s. The result returned should be identical to
	 * what would be returned by calling the specific methods (e.g.,
	 * {@link #add(Iterable)}).
	 * 
	 * @param operator
	 *            a symbolic operator
	 * @param type
	 *            the type which the resulting expression should have (since it
	 *            may not be unambiguous)
	 * @param arguments
	 *            arguments which should be appropriate for the specified
	 *            operator
	 */
	SymbolicExpression make(SymbolicOperator operator, SymbolicType type,
			SymbolicObject[] arguments);

	/**
	 * Retruns the total number of calls made to methods
	 * {@link Reasoner#valid(BooleanExpression)} and
	 * {@link Reasoner#validOrModel(BooleanExpression)}.
	 * 
	 * @return the total number of validity calls
	 */
	int numValidCalls();

	/**
	 * Returns the total number of calls made to the validity method in the
	 * underlying automated theorem prover. This is in general smaller than that
	 * returned by {@link #numValidCalls()}, as not every valid call requires a
	 * call to the prover.
	 * 
	 * @return the total number of theorem prover validity calls
	 */
	int numProverValidCalls();

	// Symbolic primitive objects: ints, boolean, reals, strings
	// Note: these are not symbolic expressions, just symbolic objects!

	/**
	 * Returns the {@link BooleanObject} wrapping the given boolean value. A
	 * {@link BooleanObject} is a {@link SymbolicObject}, so can be used as an
	 * argument of a {@link SymbolicExpression}.
	 * 
	 * @param value
	 *            <code>true</code> or <code>false</code>, the boolean value to
	 *            wrap
	 * @return the corresponding {@link BooleanObject}
	 */
	BooleanObject booleanObject(boolean value);

	/**
	 * Returns the {@link IntObject} wrapping the given Java <code>int</code>
	 * value. An {@link IntObject} is a {@link SymbolicObject} so can be used as
	 * an argument of a {@link SymbolicExpression}. It is used in cases where a
	 * "small" concrete integer is needed. For concrete integers of arbitrary
	 * size, use {@link IntegerNumber} instead and create a {@link NumberObject}
	 * .
	 * 
	 * @param value
	 *            any Java <code>int</code>
	 * @return an {@link IntObject} wrapping <code>value</code>
	 */
	IntObject intObject(int value);

	/**
	 * Returns the {@link NumberObject} wrapping the given {@link Number} value.
	 * These are SARL {@link Number}s, not {@link java.lang.Number}s. They are
	 * used to represent infinite precision, unbounded integers and rational
	 * numbers.
	 * 
	 * @param value
	 *            a SARL Number
	 * @return the {@link NumberObject} wrapping <code>value</code>
	 */
	NumberObject numberObject(Number value);

	/**
	 * Returns the {@link StringObject} wrapping the given {@link String} value.
	 * A {@link StringObject} is a {@link SymbolicObject} so can be used as an
	 * argument to a {@link SymbolicExpression}.
	 * 
	 * @param string
	 *            any Java {@link String}
	 * @return the {@link StringObject} wrapping <code>string</code>
	 */
	StringObject stringObject(String string);

	// The "null" expression...

	/**
	 * Returns the "NULL" expression. This is a non-<code>null</code> (in the
	 * Java sense of "<code>null</code>") {@link SymbolicExpression} for which
	 * the method {@link SymbolicExpression#isNull()} returns <code>true</code>.
	 * Its type is <code>null</code>, and it has 0 arguments.
	 * 
	 * @return the NULL expression
	 */
	SymbolicExpression nullExpression();

	// Symbolic constants...

	/**
	 * <p>
	 * Returns the {@link SymbolicConstant} with the given name and type. Two
	 * {@link SymbolicConstant}s are equal iff they have the same name and type.
	 * This method may use a Flyweight Pattern to return the same object if
	 * called twice with the same arguments. Or it may create a new object each
	 * time. These details are unimportant because symbolic constants are
	 * immutable.
	 * </p>
	 * 
	 * <p>
	 * This method will return the right kind of {@link SymbolicConstant} based
	 * on the type. For example, if the type is numeric (
	 * {@link SymbolicIntegerType} or {@link SymbolicRealType}), an instance of
	 * {@link NumericSymbolicConstant} will be returned. If the type is boolean,
	 * a {@link BooleanSymbolicConstant} will be returned.
	 * </p>
	 * 
	 * @param name
	 *            the name to give to this symbolic constant; it will be used to
	 *            identify the object and for printing
	 * @param type
	 *            the type of the symbolic constant
	 */
	SymbolicConstant symbolicConstant(StringObject name, SymbolicType type);

	// Integers...

	/**
	 * The symbolic expression representing the 0 integer value.
	 * 
	 * @return the integer 0 as a numeric symbolic expression
	 */
	NumericExpression zeroInt();

	/**
	 * The symbolic expression representing the integer 1.
	 * 
	 * @return the integer 1 as a numeric symbolic expression
	 */
	NumericExpression oneInt();

	/**
	 * Returns the integer symbolic expression with the given <code>int</code>
	 * value.
	 * 
	 * @param value
	 *            a Java <code>int</code>
	 * @return the symbolic expression of integer type representing that
	 *         concrete value
	 */
	NumericExpression integer(int value);

	/**
	 * Returns the numeric symbolic expression with the given <code>long</code>
	 * value.
	 * 
	 * @param value
	 *            any Java <code>long</code>
	 * @return the symbolic expression of integer type with that value
	 */
	NumericExpression integer(long value);

	/**
	 * Returns the numeric symbolic expression with the given {@link BigInteger}
	 * value. The {@link BigInteger} class is a standard Java class for
	 * representing integers of any size.
	 * 
	 * @param value
	 *            any {@link BigInteger}
	 * @return the symbolic expression of integer type with that value
	 */
	NumericExpression integer(BigInteger value);

	// Rationals...

	/**
	 * Returns the symbolic expression representing the real number 0. Note that
	 * this is NOT equal to the integer number 0, since they have different
	 * types.
	 * 
	 * @return the real number 0 as a symbolic expression
	 */
	NumericExpression zeroReal();

	/**
	 * Returns the symbolic expression representing the real number 1.
	 * 
	 * @return the real number 1 as a symbolic expression
	 */
	NumericExpression oneReal();

	/**
	 * Returns the symbolic expression of real type ({@link SymbolicRealType})
	 * representing the given <code>int</code> value. This is sometimes referred
	 * to as a "rational integer".
	 * 
	 * @param value
	 *            an Java <code>int</code>
	 * @return a concrete rational representation of this integer value;
	 *         essentially, the rational number (value/1)
	 */
	NumericExpression rational(int value);

	/**
	 * Returns the symbolic expression of real type ({@link SymbolicRealType})
	 * representing the given <code>long</code> value. This is sometimes
	 * referred to as a "rational integer".
	 * 
	 * @param value
	 *            a Java <code>long</code>
	 * @return a concrete rational representation of this <code>long</code>
	 *         value; essentially the rational number (value/1)
	 */
	NumericExpression rational(long value);

	/**
	 * Returns the symbolic expression of real type ({@link SymbolicRealType})
	 * representing the given {@link BigInteger} value. This is sometimes
	 * referred to as a "rational integer"
	 * 
	 * @param value
	 *            a Java {@link BigInteger}
	 * @return a concrete rational representation of this {@link BigInteger}
	 *         value; essentially, the rational number (value/1)
	 */
	NumericExpression rational(BigInteger value);

	/**
	 * Returns the symbolic expression of real type ({@link SymbolicRealType})
	 * representing the given <code>float</code> value.
	 * 
	 * @param value
	 *            a Java <code>float</code>
	 * @return a concrete rational representation of this <code>float</code>
	 *         value
	 */
	NumericExpression rational(float value);

	/**
	 * Returns the symbolic expression of real type ({@link SymbolicRealType})
	 * representing the given <code>double</code> value.
	 * 
	 * @param value
	 *            a Java <code>double</code>
	 * @return a concrete symbolic expression of real type representing the
	 *         <code>value</code>
	 */
	NumericExpression rational(double value);

	/**
	 * Returns the rational number obtained by dividing two integers,
	 * <code>numerator</code> and <code>denominator</code>. The result is a
	 * symbolic expression of {@link SymbolicRealType}. Note that this universe
	 * is free to transform the expression into an equivalent form, for example,
	 * by canceling any common factors.
	 * 
	 * @param numerator
	 *            a Java <code>int</code>
	 * @param denominator
	 *            a non-0 Java <code>int</code>
	 * @return the real number formed by dividing <code>numerator</code> by
	 *         <code>denominator</code>, as a symbolic expression of real type
	 */
	NumericExpression rational(int numerator, int denominator);

	/**
	 * Returns the rational number obtained by dividing two long integers. The
	 * result will have {@link SymbolicRealType}.
	 * 
	 * @param numerator
	 *            a Java <code>long</code>
	 * @param denominator
	 *            a non-0 Java <code>long</code>
	 * @return the real number formed by dividing <code>numerator</code> by
	 *         <code>denominator</code>, as a {@link NumericExpression}
	 */
	NumericExpression rational(long numerator, long denominator);

	/**
	 * Returns the rational number obtained by dividing two {@link BigInteger}s.
	 * The result will have {@link SymbolicRealType}.
	 * 
	 * @param numerator
	 *            an integer, the numerator
	 * @param denominator
	 *            a non-0 integer, the denominator
	 * @return the rational number formed by dividing <code>numerator</code> by
	 *         <code>denominator</code>, as a symbolic expression
	 */
	NumericExpression rational(BigInteger numerator, BigInteger denominator);

	// General Numbers...

	/**
	 * Returns the number factory used by this universe.
	 * 
	 * @return the number factory used by this universe
	 */
	NumberFactory numberFactory();

	/**
	 * Returns the concrete symbolic expression wrapping the given number. The
	 * type of the expression will be the "ideal" {@link SymbolicIntegerType} if
	 * <code>number</code> is an {@link IntegerNumber}, or the "ideal"
	 * {@link SymbolicRealType} if <code>number</code> is a
	 * {@link RationalNumber}.
	 * 
	 * @param number
	 *            any non-<code>null</code> SARL {@link Number}
	 * @return the concrete symbolic expression wrapping that number
	 * @see #number(NumberObject)
	 */
	NumericExpression number(Number number);

	/**
	 * Returns the concrete symbolic expression wrapping the given number
	 * object. The type of the expression will be the "ideal"
	 * {@link SymbolicIntegerType} if <code>numberObject.getNumber()</code> is
	 * an {@link IntegerNumber}, or the "ideal" {@link SymbolicRealType} if it
	 * is a {@link RationalNumber}.
	 * 
	 * @param numberObject
	 *            any non-<code>null</code> {@link NumberObject}
	 * 
	 * @see #number(Number)
	 * @see #numberObject(Number)
	 */
	NumericExpression number(NumberObject numberObject);

	/**
	 * Returns the {@link Number} value if the given symbolic expression has a
	 * concrete numerical value, else returns <code>null</code>.
	 * 
	 * @param expression
	 *            any non-<code>null</code> numeric expression
	 * @return the {@link Number} value or <code>null</code>
	 */
	Number extractNumber(NumericExpression expression);

	// Characters and string expressions:

	/**
	 * Returns a concrete symbolic expression of character type which wraps the
	 * given Java char.
	 * 
	 * 
	 * @param theChar
	 *            the Java char
	 * @return symbolic expression wrapping <code>theChar</code>
	 * 
	 * @see SymbolicType.SymbolicTypeKind#CHAR
	 * @see #characterType()
	 */
	SymbolicExpression character(char theChar);

	/**
	 * If the given expression is a concrete character expression, this returns
	 * the character value, else it returns <code>null</code>.
	 * 
	 * @param expression
	 *            a symbolic expression
	 * @return the character it wraps or <code>null</code>
	 * 
	 * @see #characterType()
	 * @see #character(char)
	 */
	Character extractCharacter(SymbolicExpression expression);

	/**
	 * Returns a symbolic expression of type array-of-char which is a literal
	 * array consisting of the sequence of characters in the given string.
	 * 
	 * @param theString
	 *            a Java string
	 * @return <code>theString</code> represented as a symbolic expression of
	 *         type array-of-char
	 * 
	 * @see SymbolicArrayType
	 * @see SymbolicType.SymbolicTypeKind#CHAR
	 * @see #character(char)
	 * @see #characterType()
	 */
	SymbolicExpression stringExpression(String theString);

	// Numeric operations...

	/**
	 * Returns a symbolic expression which is the result of adding the two given
	 * symbolic expressions. The two given expressions must have the same
	 * (numeric) type: either both integers, or both real.
	 * 
	 * @param arg0
	 *            a symbolic expression of a numeric type
	 * @param arg1
	 *            a symbolic expression of the same numeric type
	 * @return the sum arg0+arg1
	 * 
	 * @see SymbolicIntegerType
	 * @see SymbolicRealType
	 */
	NumericExpression add(NumericExpression arg0, NumericExpression arg1);

	/**
	 * Returns a symbolic expression representing the sum of the given argument
	 * sequence.
	 * 
	 * @param args
	 *            a sequence of symbolic expressions of numeric type. They must
	 *            all have the same type.
	 * @return expression representing the sum
	 * 
	 * @see #add(NumericExpression, NumericExpression)
	 * @see SymbolicIntegerType
	 * @see SymbolicRealType
	 */
	NumericExpression add(Iterable<? extends NumericExpression> args);

	/**
	 * Returns a symbolic expression which is the result of subtracting arg1
	 * from arg0. The two given expressions must have the same (numeric) type:
	 * either both integers, or both real.
	 * 
	 * @param arg0
	 *            a symbolic expression of a numeric type
	 * @param arg1
	 *            a symbolic expression of the same numeric type
	 * @return the difference, arg0-arg1
	 * 
	 * @see #add(NumericExpression, NumericExpression)
	 * @see SymbolicIntegerType
	 * @see SymbolicRealType
	 */
	NumericExpression subtract(NumericExpression arg0, NumericExpression arg1);

	/**
	 * Returns a symbolic expression which is the result of multiplying the two
	 * given symbolic expressions. The two given expressions must have the same
	 * (numeric) type: either both integers, or both real.
	 * 
	 * @param arg0
	 *            a symbolic expression of a numeric type
	 * @param arg1
	 *            a symbolic expression of the same numeric type
	 * @return arg0 * arg1, the product of arg0 and arg1.
	 * 
	 * @see #add(NumericExpression, NumericExpression)
	 * @see SymbolicIntegerType
	 * @see SymbolicRealType
	 */
	NumericExpression multiply(NumericExpression arg0, NumericExpression arg1);

	/**
	 * Returns symbolic expression representing the product of the given
	 * sequence of expressions.
	 * 
	 * @param args
	 *            symbolic expression sequence; all elements have the same
	 *            numeric type
	 * @return a symbolic expression representing the product
	 * 
	 * @see #multiply(NumericExpression, NumericExpression)
	 * @see SymbolicIntegerType
	 * @see SymbolicRealType
	 */
	NumericExpression multiply(Iterable<? extends NumericExpression> args);

	/**
	 * <p>
	 * Returns a symbolic expression which is the result of dividing arg0 by
	 * arg1. The two given expressions must have the same (numeric) type: either
	 * both integers, or both real. In the integer case, division is interpreted
	 * as "integer division", which rounds towards 0.
	 * </p>
	 * 
	 * <p>
	 * For reference, here's what C11 (Sec. 6.5.5) says about integer division:
	 * </p>
	 * 
	 * <pre>
	 * The result of the / operator is the quotient from the
	 * division of the first operand by the second; the result
	 * of the % operator is the remainder. In both operations,
	 * if the value of the second operand is zero, the behavior
	 * is undefined.
	 * 
	 * When integers are divided, the result of the / operator
	 * is the algebraic quotient with any fractional part discarded.
	 * [This is often called "truncation toward zero".]
	 * If the quotient a/b is representable, the expression
	 * (a/b)*b + a%b shall equal a; otherwise, the behavior
	 * of both a/b and a%b is undefined.
	 * </pre>
	 * 
	 * <p>
	 * Hence in C, a%b=a-(a/b)*b. Examples:
	 * <ul>
	 * <li>a=4, b=3: a/b=1, a%b=4-3=1</li>
	 * <li>a=4, b=-3: a/b=-1, a%b=4-(-1)(-3)=1</li>
	 * <li>a=-4, b=3: a/b=-1, a%b=-4-(-1)3=-1</li>
	 * <li>a=-4, b=-3: a/b=1, a%b=-4-1(-3)=-1</li>
	 * </ul>
	 * </p>
	 * 
	 * <p>
	 * Note that the sign of a/b is the same for integer or real division, i.e.,
	 * sign(a/b)=sign(a)*sign(b). The sign of a%b is sign(a).
	 * </p>
	 * 
	 * @param arg0
	 *            a symbolic expression of a numeric type
	 * @param arg1
	 *            a symbolic expression of the same numeric type
	 * @return the quotient, arg0 / arg1
	 * @see SymbolicIntegerType
	 * @see SymbolicRealType
	 */
	NumericExpression divide(NumericExpression arg0, NumericExpression arg1);

	/**
	 * Returns a symbolic expression which represents arg0 modulo arg1. The two
	 * given expressions must have the integer type.
	 * 
	 * @param arg0
	 *            a symbolic expression of integer type
	 * @param arg1
	 *            a symbolic expression of integer type
	 * @return the modulus, arg0 % arg1
	 * @see SymbolicIntegerType
	 * @see #divide(NumericExpression, NumericExpression)
	 * @see #divides(NumericExpression, NumericExpression)
	 */
	NumericExpression modulo(NumericExpression arg0, NumericExpression arg1);

	/**
	 * Returns a symbolic expression which is the negative of the given
	 * numerical expression. The given expression must be non-null and have
	 * either integer or real type.
	 * 
	 * @param arg
	 *            a symbolic expression of integer or real type
	 * @return negation: &minus; <code>arg</code>
	 * @see SymbolicIntegerType
	 * @see SymbolicRealType
	 */
	NumericExpression minus(NumericExpression arg);

	/**
	 * Concrete power operator: <i>e</i><sup><i>b</i></sup>, where <i>b</i> is a
	 * concrete non-negative integer. This method might actually multiply out
	 * the expression, i.e., it does not necessarily return an expression with
	 * operator {@link SymbolicOperator#POWER}.
	 * 
	 * @param base
	 *            the base expression in the power expression
	 * @param exponent
	 *            a non-negative concrete integer exponent
	 */
	NumericExpression power(NumericExpression base, IntObject exponent);

	/**
	 * Equivalent to <code>power(base, intObject(exponent))</code>.
	 * 
	 * @param base
	 *            the base expression in the power expression
	 * @param exponent
	 *            a non-negative concrete integer exponent
	 * @return <code>power(base, intObject(exponent))</code>
	 */
	NumericExpression power(NumericExpression base, int exponent);

	/**
	 * General power operator: <i>e</i><sup><i>b</i></sup>. Both <i>e</i> and
	 * <i>b</i> are numeric expressions.
	 * 
	 * @param base
	 *            the base expression in the power expression
	 * @param exponent
	 *            the exponent in the power expression
	 */
	NumericExpression power(NumericExpression base, NumericExpression exponent);

	// Booleans...

	/**
	 * If the given expression has a concrete {@link Boolean} value, this
	 * returns it, else it returns <code>null</code>.
	 * 
	 * @param expression
	 *            any {@link BooleanExpression}
	 * @return one of the two concrete {@link Boolean} values if
	 *         <code>expression</code> is concrete, else <code>null</code>
	 */
	Boolean extractBoolean(BooleanExpression expression);

	/**
	 * Returns the boolean literal <i>true</i>.
	 * 
	 * @return the symbolic expression <i>true</i>
	 */
	BooleanExpression trueExpression();

	/**
	 * Returns the boolean literal <i>false</i>.
	 * 
	 * @return the symbolic expression <i>false</i>
	 */
	BooleanExpression falseExpression();

	/**
	 * Notifies this universe to attempt to simplify boolean expressions as they
	 * are created, for example, by searching for clauses of the form
	 * <code>(p || !p)</code> and replacing with <code>true</code>. This can be
	 * expensive. Default is <code>false</code>.
	 * 
	 * @param value
	 *            if <code>true</code>, from now on start trying to simplify
	 *            boolean expressions; if <code>false</code>, from now on do not
	 *            attempt to do so
	 */
	void setBooleanExpressionSimplification(boolean value);

	// TODO: continue editing Java-docs from this point.....

	/**
	 * Whether or not CnfFactory methods are allowed to simplify expensive (p ||
	 * !p) expressions.
	 * 
	 * @return boolean value: false = default
	 */
	boolean getBooleanExpressionSimplification();

	/**
	 * The symbolic expression wrapping the given boolean object (true or
	 * false).
	 */
	BooleanExpression bool(BooleanObject object);

	/**
	 * Short cut for symbolic(booleanObject(value)).
	 * 
	 * @param value
	 * @return symbolic expression wrapping boolean value
	 */
	BooleanExpression bool(boolean value);

	/**
	 * Returns a symbolic expression representing the conjunction of the two
	 * given arguments. Each argument must be non-null and have boolean type.
	 * 
	 * @param arg0
	 *            a symbolic expression of boolean type
	 * @param arg1
	 *            a symbolic expression of boolean type
	 * @return conjunction of arg0 and arg1
	 */
	BooleanExpression and(BooleanExpression arg0, BooleanExpression arg1);

	/**
	 * Returns a symbolic expression which represents the conjunction of the
	 * expressions in the given array args. Each expression in args must have
	 * boolean type. args must be non-null, and may have any length, including
	 * 0. If the length of args is 0, the resulting expression is equivalent to
	 * "true".
	 * 
	 * @param args
	 *            a sequence of expressions of boolean type
	 * @return the conjunction of the expressions in args
	 */
	BooleanExpression and(Iterable<? extends BooleanExpression> args);

	/**
	 * Returns a symbolic expression representing the disjunction of the two
	 * given arguments. Each argument must be non-null and have boolean type.
	 * 
	 * @param arg0
	 *            a symbolic expression of boolean type
	 * @param arg1
	 *            a symbolic expression of boolean type
	 * @return disjunction of arg0 and arg1
	 */
	BooleanExpression or(BooleanExpression arg0, BooleanExpression arg1);

	/**
	 * Returns a symbolic expression which represents the disjunction of the
	 * expressions in the given array args. Each expression in args must have
	 * boolean type. args must be non-null, and may have any length, including
	 * 0. If the length of args is 0, the resulting expression is equivalent to
	 * "false".
	 * 
	 * @param args
	 *            a sequence of expressions of boolean type
	 * @return the disjunction of the expressions in args
	 */
	BooleanExpression or(Iterable<? extends BooleanExpression> args);

	/**
	 * Returns a symbolic expression representing the logical negation of the
	 * given expression arg. arg must be non-null and have boolean type.
	 * 
	 * @param arg
	 *            a symbolic expression of boolean type
	 * @return negation of arg
	 */
	BooleanExpression not(BooleanExpression arg);

	/**
	 * Returns a symbolic expression representing "p implies q", i.e., p=>q.
	 * 
	 * @param arg0
	 *            a symbolic expression of boolean type (p)
	 * @param arg1
	 *            a symbolic expression of boolean type (q)
	 * @return p=>q
	 */
	BooleanExpression implies(BooleanExpression arg0, BooleanExpression arg1);

	/**
	 * Returns a symbolic expression representing "p is equivalent to q", i.e.,
	 * p<=>q.
	 * 
	 * @param arg0
	 *            a symbolic expression of boolean type (p)
	 * @param arg1
	 *            a symbolic expression of boolean type (q)
	 * @return p<=>q
	 */
	BooleanExpression equiv(BooleanExpression arg0, BooleanExpression arg1);

	/**
	 * Returns expression equivalent to arg0 < arg1. The arguments must be
	 * numeric of the same type (i.e., both are of integer type or both are of
	 * real type).
	 * 
	 * @param arg0
	 *            symbolic expression of numeric type
	 * @param arg1
	 *            symbolic expression of same numeric type
	 * @return symbolic expression of boolean type arg0 < arg1
	 */
	BooleanExpression lessThan(NumericExpression arg0, NumericExpression arg1);

	/**
	 * Returns expression equivalent to arg0 <= arg1 ("less than or equal to").
	 * The arguments must be numeric of the same type (i.e., both are of integer
	 * type or both are of real type).
	 * 
	 * @param arg0
	 *            symbolic expression of numeric type
	 * @param arg1
	 *            symbolic expression of same numeric type
	 * @return symbolic expression of boolean type arg0 <= arg1
	 */
	BooleanExpression lessThanEquals(NumericExpression arg0,
			NumericExpression arg1);

	/**
	 * Returns expression equivalent to arg0 = arg1 ("equals"). This is a
	 * general equals operator (not just for numeric expressions). To be equal,
	 * the arguments must have equal types. The notion of equals then depends on
	 * the particular type.
	 * 
	 * @param arg0
	 *            a symbolic expression
	 * @param arg1
	 *            a symbolic expression
	 * @return symbolic expression of boolean type arg0 = arg1
	 */
	BooleanExpression equals(SymbolicExpression arg0, SymbolicExpression arg1);

	/**
	 * Returns expression equivalent to arg0 != arg1 ("not equals").
	 * 
	 * @param arg0
	 *            a symbolic expression
	 * @param arg1
	 *            a symbolic expression
	 * @return symbolic expression of boolean type arg0 != arg1
	 */
	BooleanExpression neq(SymbolicExpression arg0, SymbolicExpression arg1);

	/**
	 * Returns the universally quantified expression forall(x).e.
	 * 
	 * @param boundVariable
	 *            the bound variable x
	 * @param predicate
	 *            the expression e (of boolean type)
	 * @return the expression forall(x).e
	 */
	BooleanExpression forall(SymbolicConstant boundVariable,
			BooleanExpression predicate);

	/**
	 * A special case of "forall" that is very common: forall integers i such
	 * that low<=i<high, p(i).
	 * 
	 * @param index
	 *            i, a symbolic constant of integer type
	 * @param low
	 *            a symbolic expression of integer type, lower bound of i
	 *            (inclusive)
	 * @param high
	 *            a symbolic expression of integer type, upper bound of i
	 *            (exclusive)
	 * @param predicate
	 *            some boolean symbolic expression, usually involving i
	 * @return an expression equivalent to "forall int i. low<=i<high -> p(i)".
	 */
	BooleanExpression forallInt(NumericSymbolicConstant index,
			NumericExpression low, NumericExpression high,
			BooleanExpression predicate);

	/**
	 * Returns the existentially quantified expression exists(x).e.
	 * 
	 * @param boundVariable
	 *            the bound variable x
	 * @param predicate
	 *            the expression e (of boolean type)
	 * @return the expression exists(x).e
	 */
	BooleanExpression exists(SymbolicConstant boundVariable,
			BooleanExpression predicate);

	/**
	 * A special case of "exists" that is very common: exists integer i such
	 * that low<=i<high and p(i).
	 * 
	 * @param index
	 *            i, a symbolic constant of integer type
	 * @param low
	 *            a symbolic expression of integer type, lower bound of i
	 *            (inclusive)
	 * @param high
	 *            a symbolic expression of integer type, upper bound of i
	 *            (exclusive)
	 * @param predicate
	 *            some boolean symbolic expression, usually involving i
	 * @return an expression equivalent to "exists int i. low<=i<high && p(i)".
	 */
	BooleanExpression existsInt(NumericSymbolicConstant index,
			NumericExpression low, NumericExpression high,
			BooleanExpression predicate);

	/**
	 * Does the integer a divide the integer b evenly? I.e, does there exist an
	 * integer n such that b=a*n?
	 * 
	 * @param a
	 *            a symbolic expression of integer type
	 * @param b
	 *            a symbolic expression of integer type
	 * @return a symbolic expression of boolean type holding iff a divides b
	 */
	BooleanExpression divides(NumericExpression a, NumericExpression b);

	// Functions...

	/**
	 * Returns the lambda expression lambda(x).e, i.e., the expression
	 * representing the function which given x returns e, where e might possibly
	 * involve the variable x. Note that x is a symbolic constant.
	 * 
	 * @param boundVariable
	 *            the bound variable x
	 * @param expression
	 *            the expression e
	 * @return lambda(x).e
	 */
	SymbolicExpression lambda(SymbolicConstant boundVariable,
			SymbolicExpression expression);

	/**
	 * The result of applying an uninterpreted function to a sequence of
	 * arguments. The number and types of arguments must match the function's
	 * input signature.
	 */
	SymbolicExpression apply(SymbolicExpression function,
			Iterable<? extends SymbolicExpression> argumentSequence);

	// Union type operations...

	/**
	 * Casts an object belonging to one of the members of a union type to the
	 * union type.
	 * 
	 * @param unionType
	 *            the union type
	 * @param memberIndex
	 *            the index of the member type of the object in the list of
	 *            member types of the union type
	 * @param object
	 *            an expression whose type is the member type with the given
	 *            index
	 * @return an expression whose type is the union type representing the same
	 *         object as the given object
	 */
	SymbolicExpression unionInject(SymbolicUnionType unionType,
			IntObject memberIndex, SymbolicExpression object);

	/**
	 * Tests whether an object of a union type is in the image of injection from
	 * the member type of the given index.
	 * 
	 * @param memberIndex
	 *            an integer in range [0,n-1], where n is the number of member
	 *            types of the union type
	 * @param object
	 *            an expression of the union type
	 * @return a boolean expression telling whether the object belongs to the
	 *         specified member type
	 */
	BooleanExpression unionTest(IntObject memberIndex, SymbolicExpression object);

	/**
	 * Casts an object whose type is a union type to a representation whose type
	 * is the appropriate member type of the union type. The behavior is
	 * undefined if the object does not belong to the specified member type.
	 * 
	 * @param memberIndex
	 *            an integer in range [0,n-1], where n is the number of member
	 *            types of the union types
	 * @param object
	 *            an object whose type is the union type and for which
	 *            unionTest(unionType, memberIndex, object) holds.
	 * @return a representation of the object with type the member type
	 */
	SymbolicExpression unionExtract(IntObject memberIndex,
			SymbolicExpression object);

	// Arrays...

	/**
	 * <p>
	 * Creates a concrete array expression backed by the given Java array. Any
	 * changes to the Java array will also change the returned expression, so
	 * the Java array should never be modified after this method is called.
	 * </p>
	 * 
	 * <p>
	 * Precondition: every element of <code>elements</code> must have type
	 * <code>elementType</code>. This is <b>not</b> necessarily checked. If this
	 * condition is not met, behavior is undefined.
	 * </p>
	 * 
	 * @param elementType
	 *            the type of each element of <code>elements</code>
	 * @param elements
	 *            array of symbolic expressions, each of type
	 *            <code>elementType</code>
	 * @return symbolic expression of type {@link SymbolicCompleteArrayType}
	 *         with element type <code>elementType</code> and length
	 *         <code>elements.length</code> wrapping <code>elements</code>
	 */
	SymbolicExpression array(SymbolicType elementType,
			SymbolicExpression[] elements);

	/**
	 * Returns the concrete array consisting of given sequence of elements. The
	 * type of the array will be the complete array type determined by the
	 * element type and the number of elements.
	 * 
	 * @param elementType
	 *            the type of each element of the array
	 * @param elements
	 *            sequence of symbolic expressions
	 * @return array consisting of those elements
	 */
	SymbolicExpression array(SymbolicType elementType,
			Iterable<? extends SymbolicObject> elements);

	/**
	 * Returns array of length 0.
	 * 
	 * @param elementType
	 *            the type of the non-existent elements of this array
	 * @return array of length 0 of given type
	 */
	SymbolicExpression emptyArray(SymbolicType elementType);

	/**
	 * Returns an array in which every element has the same value.
	 * 
	 * @param elementType
	 *            the element type of the array
	 * @param length
	 *            the length of the array
	 * @param value
	 *            the value of each element
	 * @return an array of specified length in which every element is value
	 */
	SymbolicExpression constantArray(SymbolicType elementType,
			NumericExpression length, SymbolicExpression value);

	/**
	 * Appends an element to the end of a concrete symbolic array. Returns a new
	 * array expression which is same as old with new element appended to end.
	 * 
	 * TODO: extend to arbitrary arrays, not just concrete
	 * 
	 * @param concreteArray
	 *            a concrete array
	 * @param element
	 *            a symbolic expression whose type is compatible with element
	 *            type of the array
	 * @return an array obtained by appending element to given array
	 */
	SymbolicExpression append(SymbolicExpression concreteArray,
			SymbolicExpression element);

	/**
	 * Removes an element in a specified position in a concrete symbolic array.
	 * Returns a new array which is same as old except the element has been
	 * removed and the remaining elements have been shifted down to remove the
	 * gap. The resulting array has length 1 less than the original one.
	 * 
	 * TODO: extend to arbitrary arrays, not just concrete
	 * 
	 * @param concreteArray
	 *            a concrete array
	 * @param index
	 *            an int index
	 * @return array obtained by removing element at specified index
	 * @throws SARLException
	 *             if index is negative or greater than or equal to the length
	 *             of the given concrete array
	 */
	SymbolicExpression removeElementAt(SymbolicExpression concreteArray,
			int index);

	/**
	 * Inserts value an position index in array, shifting subsequence elements
	 * "up".
	 * 
	 * @param concreteArray
	 *            a concrete array
	 * @param index
	 *            an int index in the range [0,length], where length is the
	 *            length of the original array. If index=length, this is the
	 *            same as append.
	 * @param value
	 *            expression to insert
	 * @return array obtained by inserting the element at specified index
	 */
	SymbolicExpression insertElementAt(SymbolicExpression concreteArray,
			int index, SymbolicExpression value);

	/**
	 * Returns the length of any symbolic expression of array type. This is a
	 * symbolic expression of integer type.
	 * 
	 * @param array
	 *            a symbolic expression of array type
	 * @return a symbolic expression of integer type representing the length of
	 *         the array
	 */
	NumericExpression length(SymbolicExpression array);

	/**
	 * Returns an expression representing the value of the element of the array
	 * at position index. Arrays are indexed from 0. The expression returned has
	 * type the element type of the array.
	 * 
	 * @param array
	 *            the given array
	 * @param index
	 *            symbolic expression of integer type
	 * @return expression representing value of index-th element of the array
	 */
	SymbolicExpression arrayRead(SymbolicExpression array,
			NumericExpression index);

	/**
	 * Returns an expression representing the result of modifying an array by
	 * changing the value at position index. Arrays are indexed from 0. The
	 * expression returned has the same (array) type as the original array.
	 * 
	 * @param array
	 *            the given array
	 * @param index
	 *            symbolic expression of integer type
	 * @param value
	 *            the new value for the element at position index
	 * @return expression representing the result of changing the index-th
	 *         element to value
	 */
	SymbolicExpression arrayWrite(SymbolicExpression array,
			NumericExpression index, SymbolicExpression value);

	/**
	 * Returns an array obtained by performing a sequence of writes, given in a
	 * "dense" format, to an array. The sequence of values are used to write to
	 * the indexes 0, 1, .... A null element in the sequence is simply ignored.
	 * 
	 * @param array
	 *            a symbolic expression of array type
	 * @param values
	 *            a sequence of symbolic expressions, each of which is either
	 *            null or a symbolic expression of the appropriate type
	 * @return the array resulting from writing to the given array in position
	 *         0,...,n-1, where n is the length of the sequence.
	 */
	SymbolicExpression denseArrayWrite(SymbolicExpression array,
			Iterable<? extends SymbolicExpression> values);

	/**
	 * Returns an expression representing an array with element type T defined
	 * by a function f from int to T.
	 */
	SymbolicExpression arrayLambda(SymbolicCompleteArrayType arrayType,
			SymbolicExpression function);

	// Tuples...

	/**
	 * Returns the concrete tuple with the given members. This does NOT check
	 * that members have types compatible with the fields types of the tuple
	 * type. If they don't, the behavior is undefined.
	 * 
	 * @param type
	 *            the tuple type
	 * @param components
	 *            the component expressions
	 * @return the tuple formed from the components
	 */
	SymbolicExpression tuple(SymbolicTupleType type,
			SymbolicExpression[] components);

	/**
	 * Returns the concrete tuple expression with the given tuple components.
	 * 
	 * @param type
	 *            the tuple type
	 * @param components
	 *            the component expressions
	 * @return the tuple formed from the components
	 */
	SymbolicExpression tuple(SymbolicTupleType type,
			Iterable<? extends SymbolicObject> components);

	/**
	 * Returns an expression that represents the result of reading a component
	 * in a tuple value. The index should be an integer-valued expression. The
	 * components are numbered starting from 0.
	 * 
	 * @param tuple
	 *            the tuple value being read
	 * @param index
	 *            index of the component to read
	 * @return a symbolic expression representing the component at that index
	 */
	SymbolicExpression tupleRead(SymbolicExpression tuple, IntObject index);

	/**
	 * Returns an expression representing the result of modifying a tuple by
	 * changing the value of one component. The component is specified by its
	 * index. The components are indexed starting from 0. In this method, the
	 * index is specified by a concrete Java int.
	 * 
	 * @param tuple
	 *            the original tuple
	 * @param index
	 *            the index of the component to modify
	 * @param value
	 *            the new value for the component
	 * @return an expression representing the new tuple
	 */
	SymbolicExpression tupleWrite(SymbolicExpression tuple, IntObject index,
			SymbolicExpression value);

	// Sets...
	// Under construction...

	// SymbolicExpression emptySet(SymbolicSetType setType);

	// SymbolicExpression singletonSet(SymbolicSetType setType,
	// SymbolicExpression value);

	// BooleanExpression isElementOf(SymbolicExpression value,
	// SymbolicExpression set);

	BooleanExpression isSubsetOf(SymbolicExpression set1,
			SymbolicExpression set2);

	SymbolicExpression setAdd(SymbolicExpression set, SymbolicExpression value);

	SymbolicExpression setRemove(SymbolicExpression set,
			SymbolicExpression value);

	SymbolicExpression setUnion(SymbolicExpression set1, SymbolicExpression set2);

	SymbolicExpression setIntersection(SymbolicExpression set1,
			SymbolicExpression set2);

	SymbolicExpression setDifference(SymbolicExpression set1,
			SymbolicExpression set2);

	NumericExpression cardinality(SymbolicExpression set);

	// Maps...

	SymbolicExpression emptyMap(SymbolicMapType mapType);

	SymbolicExpression put(SymbolicExpression map, SymbolicExpression key,
			SymbolicExpression value);

	SymbolicExpression get(SymbolicExpression map, SymbolicExpression key);

	SymbolicExpression removeEntryWithKey(SymbolicExpression map,
			SymbolicExpression key);

	SymbolicExpression keySet(SymbolicExpression map);

	NumericExpression mapSize(SymbolicExpression map);

	/**
	 * Returns the entry set of the map. This is the set consisting of all
	 * ordered pairs (key,value) for each entry in the map. Each entry is a
	 * symbolic expression which has a tuple type. The tuple type has two
	 * components: component 0 is the key type, component 1 the value type.
	 * 
	 * @param map
	 * @return
	 */
	SymbolicExpression entrySet(SymbolicExpression map);

	// Misc. expressions...

	/**
	 * Casts expression to new type.
	 * 
	 * @param newType
	 *            a symbolic type
	 * @param expression
	 *            a symbolic expression
	 * @return symbolic expression cast to new type
	 */
	SymbolicExpression cast(SymbolicType newType, SymbolicExpression expression);

	/**
	 * "If-then-else" expression. Note that trueCase and falseCase must have the
	 * same type, which becomes the type of this expression.
	 * 
	 * @param predicate
	 *            the test condition p
	 * @param trueCase
	 *            the value if condition is true
	 * @param falseCase
	 *            the value if condition is false
	 * @return symbolic expression whose values is trueCase if predicate holds,
	 *         falseCase if predicate is false
	 */
	SymbolicExpression cond(BooleanExpression predicate,
			SymbolicExpression trueCase, SymbolicExpression falseCase);

	// References

	/**
	 * <p>
	 * Returns the type of all reference expressions. A reference expression is
	 * a kind of symbolic expression used to represent a reference to a
	 * subexpression of other expressions. It may be thought of as a sequence of
	 * directions for navigating to a particular node in a tree, starting from
	 * the root. For example, a reference expression <i>r</i> might encode
	 * "the 3rd element of the 2nd component". Given an expression <i>e</i> of
	 * tuple type in which the 2nd component has array type, that <i>r</i>
	 * specifies a particular element of a particular component of <i>e</i>.
	 * </p>
	 * 
	 * <p>
	 * A reference may also be thought of as a <i>function</i> which takes a
	 * symbolic expression (of a compatible type) and returns a sub-expression
	 * of that expression.
	 * </p>
	 * 
	 * @return the type of all reference expressions
	 */
	SymbolicType referenceType();

	/**
	 * Returns the "null reference", a symbolic expression of reference type
	 * which is not equal to a reference value returned by any of the other
	 * methods, and which cannot be dereferenced.
	 * 
	 * @return the null reference
	 */
	ReferenceExpression nullReference();

	/**
	 * Given a <code>reference</code> and a <code>value</code>, returns the
	 * sub-expression of <code>value</code> specified by the reference. Throws
	 * exception if the reference is not of the correct form for the type of
	 * <code>value</code>.
	 * 
	 * @param value
	 *            a non-<code>null</code> symbolic expression
	 * @param reference
	 *            a non-<code>null</code> reference into a sub-expression of
	 *            <code>value</code>
	 * @return the sub-expression of <code>value</code> specified by the
	 *         reference
	 */
	SymbolicExpression dereference(SymbolicExpression value,
			ReferenceExpression reference);

	/**
	 * Returns the type referenced by a reference into an expression of the
	 * given type. Example: if <code>type</code> is <i>array-of-integer</i> and
	 * <code>reference</code> is an array element reference, this method returns
	 * <i>integer</i>.
	 * 
	 * @param type
	 *            a non-<code>null</code> symbolic type
	 * @param reference
	 *            a reference that is compatible with <code>type</code>, i.e.,
	 *            can reference into an expression of that type
	 * @return the component of the given type which is referenced by the given
	 *         reference
	 */
	SymbolicType referencedType(SymbolicType type, ReferenceExpression reference);

	/**
	 * Returns the identity (or "trivial") reference <code>I</code>. This is the
	 * reference characterized by the property that
	 * <code>dereference(I,v)</code> returns <code>v</code> for any symbolic
	 * expression <code>v</code>.
	 * 
	 * @return the identity reference
	 */
	ReferenceExpression identityReference();

	/**
	 * Given a reference to an array and an <code>index</code> (integer),
	 * returns a reference to the element of the array at that index. Think of
	 * this as tacking on one more instruction to the sequence of directions
	 * specified by a reference. For example, if <code>arrayReference</code>
	 * encodes "2nd component of element 3" and <code>index</code> is
	 * <code>X+Y</code>, the result returned specifies "element <code>X+Y</code>
	 * of the 2nd component of element 3".
	 * 
	 * @param arrayReference
	 *            a non-<code>null</code> reference for which the referenced
	 *            sub-expression has array type
	 * @param index
	 *            a non-<code>null</code> expression of integer type
	 * @return a reference to the <code>index</code>-th element of the
	 *         referenced array
	 */
	ArrayElementReference arrayElementReference(
			ReferenceExpression arrayReference, NumericExpression index);

	/**
	 * Given a reference to a tuple, and a field index, returns a reference to
	 * that component of the tuple. Think of this as tacking on one more
	 * instruction to the sequence of directions specified by a reference. For
	 * example, if <code>tupleReference</code> encodes
	 * "2nd component of element 3" and <code>fieldIndex</code> is 15, the
	 * result returned specifies "the 15-th component of the 2nd component of
	 * element 3".
	 * 
	 * @param tupleReference
	 *            a non-<code>null</code> reference for which the referenced
	 *            sub-expression has tuple type
	 * @param fieldIndex
	 *            a non-<code>null</code> concrete integer object specifying the
	 *            component of the tuple (indexed from 0)
	 * @return a reference to the <code>fieldIndex</code>-th element of the
	 *         referenced tuple
	 */
	TupleComponentReference tupleComponentReference(
			ReferenceExpression tupleReference, IntObject fieldIndex);

	/**
	 * Given a reference to a union (expression of union type) and an index of a
	 * member type of that union, returns a reference to the underlying element.
	 */
	UnionMemberReference unionMemberReference(
			ReferenceExpression unionReference, IntObject memberIndex);

	OffsetReference offsetReference(ReferenceExpression reference,
			NumericExpression offset);

	/**
	 * Given a symbolic expression value, a reference to a point within that
	 * value, and a subValue, returns the symbolic expression obtained by
	 * replacing the referenced part of value with subValue.
	 * 
	 * @param value
	 *            a non-<code>null</code> symbolic expression
	 * @param reference
	 *            a non-<code>null</code> reference to a subexpression of
	 *            <code>value</code>
	 * @param subValue
	 *            a non-<code>null</code> expression with type compatible with
	 *            that of the referenced sub-expression of <code>value</code>
	 * @return the expression that results from taking <code>value</code> and
	 *         replacing the referenced sub-expression with
	 *         <code>subValue</code>
	 */
	SymbolicExpression assign(SymbolicExpression value,
			ReferenceExpression reference, SymbolicExpression subValue);

	/**
	 * Returns the set of unbound symbolic constants occurring in an expression.
	 * Each symbolic constant will occur at most once in the collection
	 * returned. This includes symbolic constants that occur in types (for
	 * example, array lengths).
	 * 
	 * @param expr
	 *            a non-<code>null</code> symbolic expression
	 * @return set of unbound symbolic constants occurring in <code>expr</code>
	 */
	Set<SymbolicConstant> getFreeSymbolicConstants(SymbolicExpression expr);

	/**
	 * Returns the result of bit-and operation for two given bit vectors, those
	 * two vectors are in the form of {@link SymbolicExpression}.
	 * 
	 * @param left
	 *            a non-<code>null</code> {@link SymbolicExpression}
	 *            representing an array of booleans. The length of this array
	 *            should be concrete.
	 * @param right
	 *            a non-<code>null</code> {@link SymbolicExpression}
	 *            representing an array of booleans with the same type of the
	 *            left array. And the length of this array should be concrete.
	 * @return a {@link SymbolicExpression} representing the result array.
	 */
	SymbolicExpression bitand(SymbolicExpression left, SymbolicExpression right);

	/**
	 * Returns the result of bit-or operation for two given bit vectors, those
	 * two vectors are in the form of {@link SymbolicExpression}.
	 * 
	 * @param left
	 *            a non-<code>null</code> {@link SymbolicExpression}
	 *            representing an array of booleans. The length of this array
	 *            should be concrete.
	 * @param right
	 *            a non-<code>null</code> {@link SymbolicExpression}
	 *            representing an array of booleans with the same type of the
	 *            left array. And the length of this array should be concrete.
	 * @return a {@link SymbolicExpression} representing the result array.
	 */
	SymbolicExpression bitor(SymbolicExpression left, SymbolicExpression right);

	/**
	 * Returns the result of bit-xor operation for two given bit vectors, those
	 * two vectors are in the form of {@link SymbolicExpression}.
	 * 
	 * @param left
	 *            a non-<code>null</code> {@link SymbolicExpression}
	 *            representing an array of booleans. The length of this array
	 *            should be concrete.
	 * @param right
	 *            a non-<code>null</code> {@link SymbolicExpression}
	 *            representing an array of booleans with the same type of the
	 *            left array. And the length of this array should be concrete.
	 * @return a {@link SymbolicExpression} representing the result array.
	 */
	SymbolicExpression bitxor(SymbolicExpression left, SymbolicExpression right);

	/**
	 * Returns the result of bit-not operation for the given bit vectors, the
	 * given vector is in the form of {@link SymbolicExpression}.
	 * 
	 * @param left
	 *            a non-<code>null</code> {@link SymbolicExpression}
	 *            representing an array of booleans. The length of this array
	 *            should be concrete.
	 * @return a {@link SymbolicExpression} representing the result array.
	 */
	SymbolicExpression bitnot(SymbolicExpression expression);

	/**
	 * Returns the {@link SymbolicType} representing a bitVectorType, which is
	 * an array of booleans with concrete length.
	 * 
	 * @param length
	 *            an integer representing the length of the bits of the integer
	 *            type.
	 * @return a {@link SymbolicType} with the base-type of boolean and the
	 *         given length.
	 */
	SymbolicCompleteArrayType bitVectorType(int length);

	/**
	 * Returns the conversion of a bit vector from an integer.
	 * 
	 * @param integer
	 *            a non-<code>null</code> {@link SymbolicExpression}
	 *            representing an integer.
	 * @param bitVectorType
	 *            a non-<code>null</code> {@link SymbolicCompleteArrayType}
	 *            representing the type of bit vector with a type of boolean and
	 *            a <strong>concrete</strong> length.
	 * @return a non-<code>null</code> {@link SymbolicExpression} representing a
	 *         bit vector.
	 */
	SymbolicExpression integer2Bitvector(NumericExpression integer,
			SymbolicCompleteArrayType bitVectorType);

	/**
	 * Returns the conversion of an integer from a bit vector.
	 * 
	 * @param integer
	 *            a non-<code>null</code> {@link SymbolicExpression}
	 *            representing a bit vector.
	 * 
	 * @return a non-<code>null</code> {@link SymbolicExpression} representing
	 *         an integer.
	 */
	NumericExpression bitvector2Integer(SymbolicExpression bitvector);

	/**
	 * Set error filename
	 * 
	 * @param errFile
	 *            Error file name
	 */
	void setErrFile(String errFile);

	/**
	 * Get error filename
	 */
	String getErrFile();
}
