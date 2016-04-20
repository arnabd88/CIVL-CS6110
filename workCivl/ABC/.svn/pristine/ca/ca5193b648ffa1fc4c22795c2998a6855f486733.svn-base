package edu.udel.cis.vsl.abc.token.IF;

/**
 * A concatenation represents the concatenation of a sequence of adjaced string
 * literals to form one large string literal. This takes place in translation
 * phase 7 (after preprocessing), as specified in the C11 Standard.
 * 
 * @author siegel
 * 
 */
public interface Concatenation extends Formation {

	/**
	 * Gets the number of string literal tokens which are begin concatenated.
	 * 
	 * @return the number of string literals
	 */
	int getNumConstituents();

	/**
	 * Returns the index-th string literal token in the concatenation.
	 * 
	 * @param index
	 *            an integer in the range [0, numConstitutents-1]
	 * @return
	 */
	CivlcToken getConstituent(int index);

}
