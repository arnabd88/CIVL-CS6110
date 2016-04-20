package edu.udel.cis.vsl.abc.token.common;

import edu.udel.cis.vsl.abc.token.IF.CivlcToken;
import edu.udel.cis.vsl.abc.token.IF.SourceFile;
import edu.udel.cis.vsl.abc.token.IF.TransformFormation;

public class CommonTransformFormation implements TransformFormation {

	/**
	 * A "fake" SourceFile object whose name is the name of the transformer that
	 * created the new content.
	 */
	private SourceFile transformer;

	/**
	 * A more specific name, such as a method name for a method within the
	 * transformer class, that specifies the code responsible for creating the
	 * new content.
	 */
	private String method;

	/**
	 * The token in the original source that immediately precedes the point at
	 * which the new content is inserted. May be null.
	 */
	private CivlcToken preToken = null;

	/**
	 * The token in the original source that immediately succeeds the point at
	 * which the new content is inserted. May be null.
	 */
	private CivlcToken postToken = null;

	/**
	 * Creates new transform formation with null @{link {@link #preToken} and
	 * {@link #postToken}.
	 * 
	 * @param transformer
	 *            "fake" source file object for the transformer (must be
	 *            non-null)
	 * @param method
	 *            any string identifying specific part of transformer (must be
	 *            non-null)
	 */
	public CommonTransformFormation(SourceFile transformer, String method) {
		this.transformer = transformer;
		this.method = method;
	}

	/**
	 * @return the preToken
	 */
	@Override
	public CivlcToken getPreToken() {
		return this.preToken;
	}

	/**
	 * @param preToken
	 *            the preToken to set
	 */
	@Override
	public void setPreToken(CivlcToken preToken) {
		this.preToken = preToken;
	}

	/**
	 * @return the postToken
	 */
	@Override
	public CivlcToken getPostToken() {
		return this.postToken;
	}

	/**
	 * @param postToken
	 *            the postToken to set
	 */
	@Override
	public void setPostToken(CivlcToken postToken) {
		this.postToken = postToken;
	}

	@Override
	public String suffix() {
		String result = " inserted by " + transformer.getName() + "." + method;

		if (preToken != null)
			result += " after " + preToken;
		if (postToken != null)
			result += " before " + postToken;
		return result;
	}

	@Override
	public SourceFile getLastFile() {
		return transformer;
	}
}
