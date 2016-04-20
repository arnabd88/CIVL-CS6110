package edu.udel.cis.vsl.civl.library;

import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;

/**
 * The Library class implements the common logic of library enabler and library
 * executor.
 * 
 * @author Manchun Zheng (zmanchun)
 * 
 */
public abstract class Library {

	/**
	 * The symbolic expression of one.
	 */
	protected NumericExpression one;

	/**
	 * The symbolic object of integer one.
	 */
	protected IntObject oneObject;

	/**
	 * The symbolic expression of three.
	 */
	protected NumericExpression three;

	/**
	 * The symbolic object of integer three.
	 */
	protected IntObject threeObject;

	/**
	 * The symbolic expression of two.
	 */
	protected NumericExpression two;

	/**
	 * The symbolic object of integer two.
	 */
	protected IntObject twoObject;

	/**
	 * The symbolic expression of zero.
	 */
	protected NumericExpression zero;

	/**
	 * The symbolic object of integer zero.
	 */
	protected IntObject zeroObject;

	/**
	 * The symbolic universe for symbolic computations.
	 */
	protected SymbolicUniverse universe;

	/**
	 * Returns the name associated to this library executor or enabler, for
	 * example, "stdio".
	 * 
	 * @return
	 */
	public abstract String name();

	protected Library(SymbolicUniverse universe) {
		this.universe = universe;
		this.zero = universe.zeroInt();
		this.one = universe.oneInt();
		this.two = universe.integer(2);
		this.three = universe.integer(3);
		this.zeroObject = universe.intObject(0);
		this.oneObject = universe.intObject(1);
		this.twoObject = universe.intObject(2);
		this.threeObject = universe.intObject(3);
	}
}
