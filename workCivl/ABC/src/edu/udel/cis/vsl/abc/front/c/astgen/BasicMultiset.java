package edu.udel.cis.vsl.abc.front.c.astgen;

import java.util.HashMap;
import java.util.Map;

import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType.BasicTypeKind;
import edu.udel.cis.vsl.abc.front.c.parse.CivlCParser;

/**
 * A BasicMultiset represents a set with multiplicity whose elements belong to
 * the 10 basic type specifier keywords: CHAR, SHORT, INT, LONG, FLOAT, DOUBLE,
 * SIGNED, UNSIGNED, BOOL, COMPLEX. These words can be used in certain
 * combinations to denote the basic types. The order in which the words appear
 * in a declaration does not matter, but multiplicty does (since, for example, a
 * long long int is different from a long int). Hence the C11 Standard uses the
 * mathematical notion of "multiset" (set with multiplicities) to define the
 * ways to name these types. Also, several different multisets may represent the
 * same basic type.
 * 
 * @author siegel
 * 
 */
public class BasicMultiset {

	// The 10 basic type specifier keywords:

	public final static int CHAR = CivlCParser.CHAR;
	public final static int SHORT = CivlCParser.SHORT;
	public final static int INT = CivlCParser.INT;
	public final static int LONG = CivlCParser.LONG;
	public final static int FLOAT = CivlCParser.FLOAT;
	public final static int DOUBLE = CivlCParser.DOUBLE;
	public final static int SIGNED = CivlCParser.SIGNED;
	public final static int UNSIGNED = CivlCParser.UNSIGNED;
	public final static int BOOL = CivlCParser.BOOL;
	public final static int COMPLEX = CivlCParser.COMPLEX;

	// Extra real type basic type specifier keyword
	public final static int REAL = CivlCParser.REAL;

	// The 18 basic multiset classes and their variants...

	public final static BasicMultiset CHAR_TYPE = new BasicMultiset(CHAR);
	public final static BasicMultiset SIGNED_CHAR_TYPE = new BasicMultiset(
			SIGNED, CHAR);
	public final static BasicMultiset UNSIGNED_CHAR_TYPE = new BasicMultiset(
			UNSIGNED, CHAR);
	public final static BasicMultiset SHORT_TYPE = new BasicMultiset(SHORT);
	public final static BasicMultiset SHORT_TYPE_v1 = new BasicMultiset(SIGNED,
			SHORT);
	public final static BasicMultiset SHORT_TYPE_v2 = new BasicMultiset(SHORT,
			INT);
	public final static BasicMultiset SHORT_TYPE_v3 = new BasicMultiset(SIGNED,
			SHORT, INT);
	public final static BasicMultiset UNSIGNED_SHORT_TYPE = new BasicMultiset(
			UNSIGNED, SHORT);
	public final static BasicMultiset UNSIGNED_SHORT_TYPE_v1 = new BasicMultiset(
			UNSIGNED, SHORT, INT);
	public final static BasicMultiset INT_TYPE = new BasicMultiset(INT);
	public final static BasicMultiset INT_TYPE_v1 = new BasicMultiset(SIGNED);
	public final static BasicMultiset INT_TYPE_v2 = new BasicMultiset(SIGNED,
			INT);
	public final static BasicMultiset UNSIGNED_TYPE = new BasicMultiset(
			UNSIGNED);
	public final static BasicMultiset UNSIGNED_TYPE_v1 = new BasicMultiset(
			UNSIGNED, INT);
	public final static BasicMultiset LONG_TYPE = new BasicMultiset(LONG);
	public final static BasicMultiset LONG_TYPE_v1 = new BasicMultiset(SIGNED,
			LONG);
	public final static BasicMultiset LONG_TYPE_v2 = new BasicMultiset(LONG,
			INT);
	public final static BasicMultiset LONG_TYPE_v3 = new BasicMultiset(SIGNED,
			LONG, INT);
	public final static BasicMultiset UNSIGNED_LONG_TYPE = new BasicMultiset(
			UNSIGNED, LONG);
	public final static BasicMultiset UNSIGNED_LONG_TYPE_v1 = new BasicMultiset(
			UNSIGNED, LONG, INT);
	public final static BasicMultiset LONG_LONG_TYPE = new BasicMultiset(LONG,
			LONG);
	public final static BasicMultiset LONG_LONG_TYPE_v1 = new BasicMultiset(
			SIGNED, LONG, LONG);
	public final static BasicMultiset LONG_LONG_TYPE_v2 = new BasicMultiset(
			LONG, LONG, INT);
	public final static BasicMultiset LONG_LONG_TYPE_v3 = new BasicMultiset(
			SIGNED, LONG, LONG, INT);
	public final static BasicMultiset UNSIGNED_LONG_LONG_TYPE = new BasicMultiset(
			UNSIGNED, LONG, LONG);
	public final static BasicMultiset UNSIGNED_LONG_LONG_TYPE_v1 = new BasicMultiset(
			UNSIGNED, LONG, LONG, INT);
	public final static BasicMultiset FLOAT_TYPE = new BasicMultiset(FLOAT);
	public final static BasicMultiset DOUBLE_TYPE = new BasicMultiset(DOUBLE);
	public final static BasicMultiset LONG_DOUBLE_TYPE = new BasicMultiset(
			LONG, DOUBLE);
	public final static BasicMultiset BOOL_TYPE = new BasicMultiset(BOOL);
	public final static BasicMultiset FLOAT_COMPLEX_TYPE = new BasicMultiset(
			FLOAT, COMPLEX);
	public final static BasicMultiset DOUBLE_COMPLEX_TYPE = new BasicMultiset(
			DOUBLE, COMPLEX);
	public final static BasicMultiset LONG_DOUBLE_COMPLEX_TYPE = new BasicMultiset(
			LONG, DOUBLE, COMPLEX);
	public final static BasicMultiset REAL_TYPE = new BasicMultiset(REAL);

	/**
	 * A map used to specify the "acceptable" multisets and to map any
	 * acceptable multiset to its canonical name. The keys in this map are all
	 * the acceptable multisets. The value associated to a key is the name of
	 * the basic type it represents, from the enumerated type BasicTypeKind.
	 */
	public final static Map<BasicMultiset, BasicTypeKind> acceptableMultisetMap = makeAcceptableMultisetMap();

	/**
	 * Creates and initializes the acceptableMultisetMap. The map is a
	 * constant---it never changes after this.
	 * 
	 * @return the acceptable multiset map
	 */
	public final static Map<BasicMultiset, BasicTypeKind> makeAcceptableMultisetMap() {
		Map<BasicMultiset, BasicTypeKind> map = new HashMap<BasicMultiset, BasicTypeKind>();

		map.put(CHAR_TYPE, BasicTypeKind.CHAR);
		map.put(SIGNED_CHAR_TYPE, BasicTypeKind.SIGNED_CHAR);
		map.put(UNSIGNED_CHAR_TYPE, BasicTypeKind.UNSIGNED_CHAR);
		map.put(SHORT_TYPE, BasicTypeKind.SHORT);
		map.put(SHORT_TYPE_v1, BasicTypeKind.SHORT);
		map.put(SHORT_TYPE_v2, BasicTypeKind.SHORT);
		map.put(SHORT_TYPE_v3, BasicTypeKind.SHORT);
		map.put(UNSIGNED_SHORT_TYPE, BasicTypeKind.UNSIGNED_SHORT);
		map.put(UNSIGNED_SHORT_TYPE_v1, BasicTypeKind.UNSIGNED_SHORT);
		map.put(INT_TYPE, BasicTypeKind.INT);
		map.put(INT_TYPE_v1, BasicTypeKind.INT);
		map.put(INT_TYPE_v2, BasicTypeKind.INT);
		map.put(UNSIGNED_TYPE, BasicTypeKind.UNSIGNED);
		map.put(UNSIGNED_TYPE_v1, BasicTypeKind.UNSIGNED);
		map.put(LONG_TYPE, BasicTypeKind.LONG);
		map.put(LONG_TYPE_v1, BasicTypeKind.LONG);
		map.put(LONG_TYPE_v2, BasicTypeKind.LONG);
		map.put(LONG_TYPE_v3, BasicTypeKind.LONG);
		map.put(UNSIGNED_LONG_TYPE, BasicTypeKind.UNSIGNED_LONG);
		map.put(UNSIGNED_LONG_TYPE_v1, BasicTypeKind.UNSIGNED_LONG);
		map.put(LONG_LONG_TYPE, BasicTypeKind.LONG_LONG);
		map.put(LONG_LONG_TYPE_v1, BasicTypeKind.LONG_LONG);
		map.put(LONG_LONG_TYPE_v2, BasicTypeKind.LONG_LONG);
		map.put(LONG_LONG_TYPE_v3, BasicTypeKind.LONG_LONG);
		map.put(UNSIGNED_LONG_LONG_TYPE, BasicTypeKind.UNSIGNED_LONG_LONG);
		map.put(UNSIGNED_LONG_LONG_TYPE_v1, BasicTypeKind.UNSIGNED_LONG_LONG);
		map.put(FLOAT_TYPE, BasicTypeKind.FLOAT);
		map.put(DOUBLE_TYPE, BasicTypeKind.DOUBLE);
		map.put(LONG_DOUBLE_TYPE, BasicTypeKind.LONG_DOUBLE);
		map.put(BOOL_TYPE, BasicTypeKind.BOOL);
		map.put(FLOAT_COMPLEX_TYPE, BasicTypeKind.FLOAT_COMPLEX);
		map.put(DOUBLE_COMPLEX_TYPE, BasicTypeKind.DOUBLE_COMPLEX);
		map.put(LONG_DOUBLE_COMPLEX_TYPE, BasicTypeKind.LONG_DOUBLE_COMPLEX);
		map.put(REAL_TYPE, BasicTypeKind.REAL);
		return map;
	}

	/**
	 * Given any BasicMultiset, this returns null if the multiset is not
	 * acceptable (i.e., is not one of those specified in the C11 Standard as
	 * defining a basic type), else returns the name of the basic type it
	 * represents.
	 * 
	 * @param set
	 *            a multiset of type specifier keywords
	 * @return null or the name of the basic type represented
	 */
	public final static BasicTypeKind getBasicTypeKind(BasicMultiset set) {
		return acceptableMultisetMap.get(set);
	}

	// instance variables...

	int charCount = 0;
	int shortCount = 0;
	int intCount = 0;
	int longCount = 0;
	int floatCount = 0;
	int doubleCount = 0;
	int realCount = 0;
	int signedCount = 0;
	int unsignedCount = 0;
	int boolCount = 0;
	int complexCount = 0;

	/**
	 * Creates new multiset with the given elements.
	 * 
	 * @param elements
	 *            array of ints belonging to the set of 11 basic keywords
	 */
	BasicMultiset(int[] elements) {
		for (int element : elements)
			add(element);
	}

	/**
	 * Creates new empty multiset.
	 */
	BasicMultiset() {
	}

	/**
	 * Creates new multiset with 1 element.
	 * 
	 * @param element0
	 *            one of the ints representing one of the 11 basic type
	 *            specifier keywords
	 */
	BasicMultiset(int element0) {
		add(element0);
	}

	/**
	 * Creates new multiset with 2 elements.
	 * 
	 * @param element0
	 *            one of the ints representing one of the 11 basic type
	 *            specifier keywords
	 * @param element1
	 *            one of the ints representing one of the 11 basic type
	 *            specifier keywords
	 */
	BasicMultiset(int element0, int element1) {
		add(element0);
		add(element1);
	}

	/**
	 * Creates new multiset with 3 elements.
	 * 
	 * @param element0
	 *            one of the ints representing one of the 11 basic type
	 *            specifier keywords
	 * @param element1
	 *            one of the ints representing one of the 11 basic type
	 *            specifier keywords
	 * 
	 * @param element2
	 *            one of the ints representing one of the 11 basic type
	 *            specifier keywords
	 */
	BasicMultiset(int element0, int element1, int element2) {
		add(element0);
		add(element1);
		add(element2);
	}

	/**
	 * Creates new multiset with 4 elements.
	 * 
	 * @param element0
	 *            one of the ints representing one of the 11 basic type
	 *            specifier keywords
	 * @param element1
	 *            one of the ints representing one of the 11 basic type
	 *            specifier keywords
	 * 
	 * @param element2
	 *            one of the ints representing one of the 11 basic type
	 *            specifier keywords
	 * 
	 * @param element3
	 *            one of the ints representing one of the 11 basic type
	 *            specifier keywords
	 */
	BasicMultiset(int element0, int element1, int element2, int element3) {
		add(element0);
		add(element1);
		add(element2);
		add(element3);
	}

	/**
	 * Adds one element to the multiset
	 * 
	 * @param element
	 *            one of the ints representing one of the 10 basic type
	 *            specifier keywords
	 * 
	 * @exception IllegalArgumentException
	 *                if element is not one of the 10 ints representing a basic
	 *                type specifier keyword
	 */
	public void add(int element) {
		switch (element) {
		case CHAR:
			charCount++;
			break;
		case SHORT:
			shortCount++;
			break;
		case INT:
			intCount++;
			break;
		case LONG:
			longCount++;
			break;
		case FLOAT:
			floatCount++;
			break;
		case DOUBLE:
			doubleCount++;
			break;
		case REAL:
			realCount++;
			break;
		case SIGNED:
			signedCount++;
			break;
		case UNSIGNED:
			unsignedCount++;
			break;
		case BOOL:
			boolCount++;
			break;
		case COMPLEX:
			complexCount++;
			break;
		default:
			throw new IllegalArgumentException("Unknown specifier: " + element);
		}
	}

	@Override
	public int hashCode() {
		return size();
	}

	/**
	 * Returns the number of elements of the multiset.
	 * 
	 * @return the number of elements
	 */
	public int size() {
		return charCount + shortCount + intCount + longCount + floatCount
				+ doubleCount + realCount + signedCount + unsignedCount
				+ boolCount + complexCount;
	}

	/**
	 * Does this multiset equal the given one? (I.e., have the same number of
	 * elements with same multiplicity).
	 */
	@Override
	public boolean equals(Object object) {
		if (object instanceof BasicMultiset) {
			BasicMultiset that = (BasicMultiset) object;

			return charCount == that.charCount && intCount == that.intCount
					&& longCount == that.longCount
					&& floatCount == that.floatCount
					&& doubleCount == that.doubleCount
					&& signedCount == that.signedCount
					&& unsignedCount == that.unsignedCount
					&& boolCount == that.boolCount
					&& realCount == that.realCount;
		}
		return false;
	}
}
