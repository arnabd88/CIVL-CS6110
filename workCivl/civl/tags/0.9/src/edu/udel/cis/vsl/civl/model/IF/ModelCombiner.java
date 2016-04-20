package edu.udel.cis.vsl.civl.model.IF;

/**
 * A model combiner takes two models and creates a single composite model for
 * comparative symbolic execution.
 * 
 * @author zirkel
 */
public interface ModelCombiner {

	/**
	 * Combine models by creating a new system function whose outermost scope
	 * contains the system functions of the original models, all input
	 * variables, and all (renamed) output variables. The body of the new
	 * function will spawn both original system functions, wait for them to
	 * complete, and then assert the equality of corresponding output variables.
	 * 
	 * @param model0
	 *            The specification model.
	 * @param model1
	 *            The implementation model.
	 * @return The composite model.
	 */
	Model combine(Model model0, Model model1);
}
