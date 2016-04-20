package edu.udel.cis.vsl.civl.err;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Sourceable;

/**
 * An exception thrown when there is not necessarily anything wrong with the
 * program begin verified, but some CIVL feature has not yet been implemented.
 * 
 * @author siegel
 * 
 */
public class CIVLUnimplementedFeatureException extends CIVLException {

	/** Generated ID. */
	private static final long serialVersionUID = -4225986290508573575L;

	public CIVLUnimplementedFeatureException(String feature, CIVLSource source) {
		super("This feature is not yet implemented: " + feature, source);
	}

	public CIVLUnimplementedFeatureException(String feature,
			Sourceable sourceable) {
		this(feature, sourceable.getSource());
	}

	public CIVLUnimplementedFeatureException(String feature) {
		this(feature, (CIVLSource) null);
	}

}
