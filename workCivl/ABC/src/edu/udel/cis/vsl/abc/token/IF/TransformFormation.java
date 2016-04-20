package edu.udel.cis.vsl.abc.token.IF;

/**
 * Represents the formation of new tokens by a transformer. A transformer is
 * used to manipulate an AST, and in the process of doing so, may create new
 * content that does not have any origin in the actual source code. A transform
 * formation provides useful information about the origin of the new context:
 * the name of the transformer that created it, the method (or other helpful
 * identifier) that more specifically locates the code in the transformer that
 * created the new content, the actual source token that immediately
 * proceeds/follows the inserted content.
 * 
 * @author siegel
 * 
 */
public interface TransformFormation extends Formation {

	CivlcToken getPreToken();

	void setPreToken(CivlcToken preToken);

	CivlcToken getPostToken();

	void setPostToken(CivlcToken postToken);

}
