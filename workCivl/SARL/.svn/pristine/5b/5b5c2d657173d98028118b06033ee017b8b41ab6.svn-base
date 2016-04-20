/*******************************************************************************
 * Copyright (c) 2013 Stephen F. Siegel, University of Delaware.
 * 
 * This file is part of SARL.
 * 
 * SARL is free software: you can redistribute it and/or modify it under the
 * terms of the GNU Lesser General Public License as published by the Free
 * Software Foundation, either version 3 of the License, or (at your option) any
 * later version.
 * 
 * SARL is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR
 * A PARTICULAR PURPOSE. See the GNU Lesser General Public License for more
 * details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with SARL. If not, see <http://www.gnu.org/licenses/>.
 ******************************************************************************/
package edu.udel.cis.vsl.sarl.IF;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertSame;
import static org.junit.Assert.assertTrue;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

public class ArrayTest {

	private static PrintStream out = System.out;
	private SymbolicUniverse universe;
	private StringObject a_obj; // "a"
	private StringObject b_obj; // "b"
	private SymbolicType integerType;
	private NumericExpression zero, one, two, three, five, six, seventeen; // integer
																			// constants
	private List<NumericExpression> list1; // {5,6}
	private List<NumericExpression> list2; // {17}
	private List<NumericExpression> list3; // {}

	private SymbolicExpression write2d(SymbolicExpression array,
			NumericExpression i, NumericExpression j,
			SymbolicExpression value) {
		SymbolicExpression row = universe.arrayRead(array, i);
		SymbolicExpression newRow = universe.arrayWrite(row, j, value);

		return universe.arrayWrite(array, i, newRow);
	}

	private SymbolicExpression read2d(SymbolicExpression array,
			NumericExpression i, NumericExpression j) {
		SymbolicExpression row = universe.arrayRead(array, i);

		return universe.arrayRead(row, j);
	}

	@Before
	public void setUp() throws Exception {
		universe = SARL.newStandardUniverse();
		integerType = universe.integerType();
		a_obj = universe.stringObject("a");
		b_obj = universe.stringObject("b");
		zero = universe.integer(0);
		one = universe.integer(1);
		two = universe.integer(2);
		three = universe.integer(3);
		five = universe.integer(5);
		six = universe.integer(6);
		seventeen = universe.integer(17);
		list1 = Arrays.asList(new NumericExpression[] { five, six });
		list2 = Arrays.asList(new NumericExpression[] { seventeen });
		list3 = Arrays.asList(new NumericExpression[] { });
	}

	@After
	public void tearDown() throws Exception {
	}

	@Test
	public void writeAndReadTest() {
		SymbolicExpression a = universe.symbolicConstant(a_obj,
				universe.arrayType(integerType));
		NumericExpression b = (NumericExpression) universe
				.symbolicConstant(b_obj, integerType);
		NumericExpression j = universe.integer(1);
		SymbolicExpression c = universe.arrayWrite(a, j, b);
		SymbolicExpression d = universe.arrayRead(c, j);
		assertEquals(b, d);
	}

	@Test
	public void appendTest() {

		SymbolicExpression a = universe.array(integerType, list1);
		SymbolicExpression b = universe.symbolicConstant(b_obj, integerType);
		SymbolicExpression c = universe.append(a, b);

		NumericExpression aLenPlusOne = universe.add(universe.length(a), one);
		assertEquals(aLenPlusOne, universe.length(c));

		SymbolicExpression d = universe.arrayRead(c, universe.length(a));
		assertEquals(b, d);

	}

	@Test
	public void append2DTest() {
		List<SymbolicExpression> lists = new ArrayList<SymbolicExpression>();
		lists.add(universe.array(integerType, list1));
		SymbolicExpression a1 = universe.array(universe.arrayType(integerType),
				lists);
		SymbolicExpression a2 = universe.append(a1,
				universe.array(integerType, list2));
		SymbolicExpression r1 = universe.arrayRead(a2, one);
		SymbolicExpression r2 = universe.arrayRead(a2, zero);
		NumericExpression v1 = (NumericExpression) universe.arrayRead(r1, zero);
		NumericExpression v2 = (NumericExpression) universe.arrayRead(r2, one);

		assertEquals(two, universe.length(a2));
		assertEquals(seventeen, v1);
		assertEquals(six, v2);
	}

	@Test
	public void appendEmptyArrayTest() {
		SymbolicExpression a = universe.emptyArray(integerType);
		NumericExpression b = (NumericExpression) universe
				.symbolicConstant(b_obj, integerType);
		SymbolicExpression c = universe.append(a, b);
		SymbolicExpression d = universe.arrayRead(c, zero);

		assertEquals(universe.length(c), one);
		assertEquals(b, d);
	}

	@Test
	public void removeElementTest() {
		List<SymbolicExpression> lists = new ArrayList<SymbolicExpression>();
		lists.add(universe.array(integerType, list1));
		lists.add(universe.array(integerType, list2));
		lists.add(universe.array(integerType, list3));
		SymbolicExpression a1 = universe.array(universe.arrayType(integerType),
				lists);
		SymbolicExpression a2 = universe.removeElementAt(a1, 2);
		SymbolicExpression r1 = universe.arrayRead(a2, zero);
		SymbolicExpression r2 = universe.removeElementAt(r1, 0);
		SymbolicExpression a3 = universe.arrayWrite(a2, zero, r2);
		SymbolicExpression r3 = universe.arrayRead(a3, zero);
		NumericExpression v1 = (NumericExpression)universe.arrayRead(r3, zero);
		
		assertEquals(universe.length(a1), universe.add(universe.length(a3), one));
		assertEquals(universe.length(r1), universe.add(universe.length(r3), one));
		assertEquals(six, v1);
	}

	@Test
	public void insertElementTest() {

		SymbolicExpression a = universe.array(integerType, list1);
		SymbolicExpression b = universe.symbolicConstant(b_obj, integerType);
		SymbolicExpression c = universe.insertElementAt(a, 1, b);
		NumericExpression aLenPlusOne = universe.add(universe.length(a), one);
		SymbolicExpression d = universe.arrayRead(c, one);

		assertEquals(universe.length(c), aLenPlusOne);
		assertEquals(b, d);
	}

	@Test
	public void constantArrayTest() {
		SymbolicExpression a = universe.symbolicConstant(a_obj, integerType);
		SymbolicExpression b = universe.constantArray(integerType, three, a);

		assertEquals(universe.arrayRead(b, zero), a);
		assertEquals(universe.arrayRead(b, one), a);
		assertEquals(universe.arrayRead(b, two), a);
		assertEquals(three, universe.length(b));
	}

	@Test
	public void arrayWrite2Test() {
		SymbolicArrayType t1 = universe.arrayType(integerType);
		SymbolicArrayType t2 = universe.arrayType(t1, universe.integer(2));
		SymbolicExpression a1 = universe.array(integerType, list1);
		SymbolicExpression a2 = universe.array(integerType, list2);
		SymbolicExpression a = universe.symbolicConstant(a_obj, t2);

		assertTrue(t2.isComplete());
		a = universe.arrayWrite(a, zero, a1);
		a = universe.arrayWrite(a, one, a2);
		out.println("jagged1: a = " + a);
		assertEquals(five,
				universe.arrayRead(universe.arrayRead(a, zero), zero));
		assertEquals(six, universe.arrayRead(universe.arrayRead(a, zero), one));
		assertEquals(seventeen,
				universe.arrayRead(universe.arrayRead(a, one), zero));
		assertTrue(((SymbolicArrayType) a.type()).isComplete());
		assertEquals(two, universe.length(a));
		assertEquals(two, universe.length(universe.arrayRead(a, zero)));
		assertEquals(one, universe.length(universe.arrayRead(a, one)));
	}

	/**
	 * Write and read a 2d array.
	 */
	@Test
	public void array2dTest() {
		SymbolicArrayType t = universe
				.arrayType(universe.arrayType(integerType));
		SymbolicExpression a = universe.symbolicConstant(a_obj, t);
		NumericExpression zero = universe.integer(0);
		NumericExpression twoInt = universe.integer(2);
		SymbolicExpression read;

		a = write2d(a, zero, zero, twoInt);
		read = read2d(a, zero, zero);
		assertEquals(twoInt, read);
		// for the heck of it...
		out.println("array2d: new row is: " + universe.arrayRead(a, zero));
	}

	@Test
	public void denseArrayWriteTest() {
		SymbolicArrayType t = universe.arrayType(integerType);
		SymbolicExpression a = universe
				.symbolicConstant(universe.stringObject("a"), t);
		SymbolicExpression b1 = universe.denseArrayWrite(a,
				Arrays.asList(new SymbolicExpression[] { null, null, two, null,
						two, null, null }));
		SymbolicExpression b2 = universe.arrayWrite(a, two, two);

		b2 = universe.arrayWrite(b2, universe.integer(4), two);
		out.println("b1 = " + b1);
		out.println("b2 = " + b2);
		assertEquals(b2, b1);
	}

	@Test
	public void canonic1() {
		SymbolicArrayType t1 = universe.arrayType(integerType,
				universe.integer(3));
		SymbolicArrayType t2 = universe.arrayType(integerType,
				universe.integer(3));
		assertEquals(t1, t2);
		t1 = (SymbolicArrayType) universe.canonic(t1);
		t2 = (SymbolicArrayType) universe.canonic(t2);
		assertSame(t1, t2);
	}

}
