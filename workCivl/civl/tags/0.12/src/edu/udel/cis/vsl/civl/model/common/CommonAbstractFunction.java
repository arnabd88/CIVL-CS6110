package edu.udel.cis.vsl.civl.model.common;

import java.io.PrintStream;
import java.util.Iterator;
import java.util.List;

import edu.udel.cis.vsl.civl.model.IF.AbstractFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

public class CommonAbstractFunction extends CommonFunction implements
		AbstractFunction {

	private int continuity;

	/**
	 * An abstract function.
	 * 
	 * @param source
	 *            The CIVL source of the function
	 * @param name
	 *            The name of this function.
	 * @param parameters
	 *            The list of parameters.
	 * @param returnType
	 *            The return type of this function.
	 * @param containingScope
	 *            The scope containing this function.
	 * @param continuity
	 *            The total number of partial derivatives of this function that
	 *            may be taken.
	 * @param factory
	 *            The model factory
	 */
	public CommonAbstractFunction(CIVLSource source, Identifier name,
			List<Variable> parameters, CIVLType returnType,
			Scope containingScope, int continuity, ModelFactory factory) {
		super(source, name, parameters, returnType, containingScope, null,
				factory);
		this.continuity = continuity;
	}

	@Override
	public int continuity() {
		return continuity;
	}

	/* ********************** Methods from CIVLFunction ******************** */

	@Override
	public void print(String prefix, PrintStream out, boolean isDebug) {
		Iterator<Variable> iter;

		out.println(prefix + "abstract function " + this.name());
		out.println(prefix + "| continuous " + continuity);
		if (this.precondition() != null) {
			out.println(prefix + "| requires " + this.precondition());
		}
		if (this.postcondition() != null) {
			out.println(prefix + "| ensures " + this.postcondition());
		}
		out.println(prefix + "| formal parameters");
		iter = this.parameters().iterator();
		while (iter.hasNext()) {
			out.println(prefix + "| | " + iter.next().name());
		}
		this.outerScope().print(prefix + "| ", out, isDebug);
		out.flush();
	}
	
	@Override
	public boolean isAbstract(){
		return true;
	}
	
	@Override
	public boolean isNormal() {
		return false;
	}

}
