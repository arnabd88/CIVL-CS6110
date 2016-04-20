package edu.udel.cis.vsl.abc.token.IF;

/**
 * A character token represents a character constant in a source program, e.g.,
 * <code>'a'</code>. Each character constant represents a unique
 * "execution character" in the execution character set.
 * 
 * @author siegel
 * 
 */
public interface CharacterToken extends CivlcToken {

	/**
	 * Returns the execution character which this character constant represents
	 * 
	 * @return the execution character
	 */
	ExecutionCharacter getExecutionCharacter();

}
