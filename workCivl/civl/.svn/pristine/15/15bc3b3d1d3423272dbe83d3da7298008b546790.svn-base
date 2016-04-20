/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.program.IF.Program;
import edu.udel.cis.vsl.gmc.CommandLineException;
import edu.udel.cis.vsl.gmc.GMCSection;

/**
 * Class to provide translation from an AST to a model.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public interface ModelBuilder {

	/**
	 * @return The model factory used by this model builder.
	 */
	ModelFactory factory();

	/**
	 * Builds the model.
	 * 
	 * @param config
	 *            The GMC configuration
	 * @param program
	 *            The ABC program to translate
	 * @param name
	 *            The name of the model
	 * @param debugging
	 * @param debugOut
	 * @return The model.
	 * @throws CommandLineException
	 *             if an input variable initial value specified on the command
	 *             line has a type which is not compatible with the type of the
	 *             variable
	 */
	Model buildModel(GMCSection config, Program program, String name,
			boolean debugging, PrintStream debugOut)
			throws CommandLineException;

}
