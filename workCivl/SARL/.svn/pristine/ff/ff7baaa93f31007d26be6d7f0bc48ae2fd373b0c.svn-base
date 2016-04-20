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
import static org.junit.Assert.assertFalse;

import java.io.PrintStream;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

public class HerbrandTest {

	public final static PrintStream out = System.out;
	public final static boolean debug = false;
	private SymbolicUniverse universe;
	private NumericExpression x, y;
	private StringObject x_obj, y_obj;
	private SymbolicType herbrandType;

	@Before
	public void setUp() throws Exception {
		// this.universe = Universes.newHerbrandUniverse();
		universe = SARL.newStandardUniverse();
		x_obj = universe.stringObject("x");
		y_obj = universe.stringObject("y");
		herbrandType = universe.herbrandRealType();
		x = (NumericExpression) universe.symbolicConstant(x_obj, herbrandType);
		y = (NumericExpression) universe.symbolicConstant(y_obj, herbrandType);
	}

	@After
	public void tearDown() throws Exception {
	}

	/**
	 * Test adding two concrete herbrand integer (1h+2h), (2h+1h).
	 */
	@Test
	public void addConcreteTest() {
		SymbolicType herbrandInt = universe.herbrandIntegerType();
		NumericExpression one = universe.integer(1);
		NumericExpression herbOne = (NumericExpression) universe
				.cast(herbrandInt, one);
		NumericExpression two = universe.integer(2);
		NumericExpression herbTwo = (NumericExpression) universe
				.cast(herbrandInt, two);
		NumericExpression a = universe.add(herbOne, herbTwo);
		NumericExpression b = universe.add(herbTwo, herbOne);

		if (debug) {
			out.println("test12: a = " + a);
			out.println("test12: b = " + b);
		}
		assertFalse(a.equals(b));
	}

	/**
	 * Test adding two symbolic herbrand real PLUS_REAL(x+y), PLUS_REAL(y+x).
	 */
	@Test
	public void addSymbolicTest() {
		NumericExpression e1 = universe.add(x, y);
		NumericExpression e2 = universe.add(y, x);
		NumericExpression e3 = universe.add(x, y);

		if (debug) {
			out.println("test12: e1 = " + e1);
			out.println("test12: e2 = " + e2);
			out.println("test12: e3 = " + e3);
		}
		assertFalse(e1.equals(e2));
		assertEquals(e1, e3);
	}

	/**
	 * Test multiplying two concrete herbrand integer PLUS_REAL(x+y),
	 * PLUS_REAL(y+x).
	 */
	@Test
	public void multiplyConcreteTest() {
		SymbolicType herbrandInt = universe.herbrandIntegerType();
		NumericExpression one = universe.integer(1);
		NumericExpression herbOne = (NumericExpression) universe
				.cast(herbrandInt, one);
		NumericExpression two = universe.integer(2);
		NumericExpression herbTwo = (NumericExpression) universe
				.cast(herbrandInt, two);
		NumericExpression a = universe.multiply(herbOne, herbTwo);
		NumericExpression b = universe.multiply(herbTwo, herbOne);

		assertFalse(a.equals(b));
	}

	/**
	 * Test multiplying two symbolic herbrand real PLUS_REAL(x+y),
	 * PLUS_REAL(y+x).
	 */
	@Test
	public void multiplySymbolicTest() {
		NumericExpression e1 = universe.multiply(x, y);
		NumericExpression e2 = universe.multiply(y, x);
		NumericExpression e3 = universe.multiply(x, y);

		assertFalse(e1.equals(e2));
		assertEquals(e1, e3);
	}
}
