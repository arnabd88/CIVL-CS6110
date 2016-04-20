package edu.udel.cis.vsl.civl.library.common;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.log.IF.CIVLExecutionException;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.Certainty;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.CIVLTypeFactory;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.sarl.IF.SARLException;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;

/**
 * The LibraryComponent class provides the common data and operations of library
 * evaluator, enabler, and executor.
 * 
 * @author Manchun Zheng (zmanchun)
 * 
 */
public abstract class LibraryComponent {

	// The order of these operations should be consistent with civlc.cvh
	// file.
	protected enum CIVLOperator {
		CIVL_NO_OP, // no operation
		CIVL_MAX, // maxinum
		CIVL_MIN, // minimun
		CIVL_SUM, // sum
		CIVL_PROD, // product
		CIVL_LAND, // logical and
		CIVL_BAND, // bit-wise and
		CIVL_LOR, // logical or
		CIVL_BOR, // bit-wise or
		CIVL_LXOR, // logical exclusive or
		CIVL_BXOR, // bit-wise exclusive or
		CIVL_MINLOC, // min value and location
		CIVL_MAXLOC, // max value and location
		CIVL_REPLACE // replace ? TODO: Find definition for this operation
	}

	/**
	 * Operators:
	 * 
	 * <pre>
	 *   _NO_OP,  // no operation
	 *   _MAX,    // maxinum
	 *   _MIN,    // minimun
	 *   _SUM,    // sum
	 *   _PROD,   // product
	 *   _LAND,   // logical and
	 *   _BAND,   // bit-wise and
	 *   _LOR,    // logical or
	 *   _BOR,    // bit-wise or
	 *   _LXOR,   // logical exclusive or
	 *   _BXOR,   // bit-wise exclusive or
	 *   _MINLOC, // min value and location
	 *   _MAXLOC, // max value and location
	 *   _REPLACE // replace ? TODO: Find definition for this operation
	 * </pre>
	 * */
	private final int _NO_OP = 0;
	private final int _MAX = 1;
	private final int _MIN = 2;
	private final int _SUM = 3;
	private final int _PROD = 4;
	private final int _LAND = 5;
	private final int _BAND = 6;
	private final int _LXOR = 7;
	private final int _BXOR = 8;
	private final int _MINLOC = 9;
	private final int _MAXLOC = 10;
	// private final int _REPLACE = 11;

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
	 * The symbolic universe for symbolic computations.
	 */
	protected SymbolicUtility symbolicUtil;

	/**
	 * The symbolic analyzer for operations on symbolic expressions and states.
	 */
	protected SymbolicAnalyzer symbolicAnalyzer;

	protected String name;

	protected BooleanExpression trueValue;
	protected BooleanExpression falseValue;

	protected LibraryEvaluatorLoader libEvaluatorLoader;

	/**
	 * The model factory of the system.
	 */
	protected ModelFactory modelFactory;

	/**
	 * The static model of the program.
	 */
	protected Model model;

	// protected boolean statelessPrintf;

	protected CIVLTypeFactory typeFactory;

	/**
	 * The CIVL configuration object
	 */
	protected CIVLConfiguration civlConfig;

	/**
	 * Creates a new instance of a library.
	 * 
	 * @param universe
	 *            The symbolic universe to be used.
	 * @param symbolicUtil
	 *            The symbolic utility to be used.
	 * @param symbolicAnalyzer
	 *            The symbolic analyzer to be used.
	 */
	protected LibraryComponent(String name, SymbolicUniverse universe,
			SymbolicUtility symbolicUtil, SymbolicAnalyzer symbolicAnalyzer,
			CIVLConfiguration civlConfig,
			LibraryEvaluatorLoader libEvaluatorLoader, ModelFactory modelFactory) {
		this.name = name;
		this.universe = universe;
		this.zero = universe.zeroInt();
		this.one = universe.oneInt();
		this.two = universe.integer(2);
		this.three = universe.integer(3);
		this.zeroObject = universe.intObject(0);
		this.oneObject = universe.intObject(1);
		this.twoObject = universe.intObject(2);
		this.threeObject = universe.intObject(3);
		this.symbolicUtil = symbolicUtil;
		this.symbolicAnalyzer = symbolicAnalyzer;
		this.trueValue = universe.trueExpression();
		this.falseValue = universe.falseExpression();
		this.libEvaluatorLoader = libEvaluatorLoader;
		this.modelFactory = modelFactory;
		this.model = modelFactory.model();
		this.typeFactory = modelFactory.typeFactory();
		this.civlConfig = civlConfig;
	}

	/**
	 * Returns the name associated to this library executor or enabler, for
	 * example, "stdio".
	 * 
	 * @return
	 */
	public String name() {
		return this.name;
	}

	/**
	 * Completing an operation (which is included in CIVLOperation enumerator).
	 * 
	 * @author Ziqing Luo
	 * @param arg0
	 *            The new data got from the bundle
	 * @param arg1
	 *            The data has already been received previously
	 * @param op
	 *            The CIVL Operation
	 * @return
	 */
	protected SymbolicExpression applyCIVLOperator(State state, String process,
			SymbolicExpression arg0, SymbolicExpression arg1, CIVLOperator op,
			CIVLSource civlsource) {
		BooleanExpression claim;
		SymbolicExpression[] operands = { arg0, arg1 };
		SymbolicExpression[] tmpOperands = new SymbolicExpression[2];

		/*
		 * For MAX and MIN operation, if CIVL cannot figure out a concrete
		 * result, make a abstract function for it.
		 */
		try {
			switch (op) {
			// TODO: consider using heuristic to switch to abstract
			// functions if these expressions get too big (max,min):
			case CIVL_MAX:
				claim = universe.lessThan((NumericExpression) arg1,
						(NumericExpression) arg0);
				return universe.cond(claim, arg0, arg1);
			case CIVL_MIN:
				claim = universe.lessThan((NumericExpression) arg0,
						(NumericExpression) arg1);
				return universe.cond(claim, arg0, arg1);
			case CIVL_SUM:
				return universe.add((NumericExpression) arg0,
						(NumericExpression) arg1);
			case CIVL_PROD:
				return universe.multiply((NumericExpression) arg0,
						(NumericExpression) arg1);
			case CIVL_LAND:
				return universe.and((BooleanExpression) arg0,
						(BooleanExpression) arg1);
			case CIVL_LOR:
				return universe.or((BooleanExpression) arg0,
						(BooleanExpression) arg1);
			case CIVL_LXOR:
				BooleanExpression notNewData = universe
						.not((BooleanExpression) arg0);
				BooleanExpression notPrevData = universe
						.not((BooleanExpression) arg1);

				//TODO change to andTo
				return universe.or(
						universe.and(notNewData, (BooleanExpression) arg1),
						universe.and((BooleanExpression) arg0, notPrevData));
			case CIVL_BAND:
			case CIVL_BOR:
			case CIVL_BXOR:
			case CIVL_MINLOC:
				assert (operands.length == 2);
				for (int i = 0; i < operands.length; i++)
					if (operands[i].type() instanceof SymbolicTupleType)
						tmpOperands[i] = universe.tupleRead(operands[i],
								universe.intObject(0));
					else if (operands[i].type() instanceof SymbolicArrayType)
						tmpOperands[i] = universe.arrayRead(operands[i],
								universe.zeroInt());
					else
						throw new CIVLInternalException(
								"CIVL_MINLOC operations cannot resolve operands",
								civlsource);
				claim = universe.lessThan((NumericExpression) tmpOperands[0],
						(NumericExpression) tmpOperands[1]);
				return universe.cond(claim, operands[0], operands[1]);
			case CIVL_MAXLOC:
				assert (operands.length == 2);
				for (int i = 0; i < operands.length; i++)
					if (operands[i].type() instanceof SymbolicTupleType)
						tmpOperands[i] = universe.tupleRead(operands[i],
								universe.intObject(0));
					else if (operands[i].type() instanceof SymbolicArrayType)
						tmpOperands[i] = universe.arrayRead(operands[i],
								universe.zeroInt());
					else
						throw new CIVLInternalException(
								"CIVL_MAXLOC operations cannot resolve operands",
								civlsource);
				claim = universe.lessThan((NumericExpression) tmpOperands[0],
						(NumericExpression) tmpOperands[1]);
				return universe.cond(claim, operands[1], operands[0]);
			case CIVL_REPLACE:
			default:
				throw new CIVLUnimplementedFeatureException("CIVLOperation: "
						+ op.name());
			}
		} catch (ClassCastException e) {
			throw new CIVLExecutionException(ErrorKind.OTHER,
					Certainty.PROVEABLE, process,
					"Invalid operands type for CIVL Operation: " + op.name(),
					civlsource);
		} catch (SARLException e) {
			throw new CIVLInternalException("CIVL Operation " + op
					+ " exception", civlsource);
		}
	}

	protected CIVLOperator translateOperator(int op) {
		switch (op) {
		case _NO_OP:
			return CIVLOperator.CIVL_NO_OP;
		case _MAX:
			return CIVLOperator.CIVL_MAX;
		case _MIN:
			return CIVLOperator.CIVL_MIN;
		case _SUM:
			return CIVLOperator.CIVL_SUM;
		case _PROD:
			return CIVLOperator.CIVL_PROD;
		case _LAND:
			return CIVLOperator.CIVL_LAND;
		case _BAND:
			return CIVLOperator.CIVL_BAND;
		case _LXOR:
			return CIVLOperator.CIVL_LXOR;
		case _BXOR:
			return CIVLOperator.CIVL_BXOR;
		case _MINLOC:
			return CIVLOperator.CIVL_MINLOC;
		case _MAXLOC:
			return CIVLOperator.CIVL_MAXLOC;
		default:
			return CIVLOperator.CIVL_REPLACE;
		}
	}

}
