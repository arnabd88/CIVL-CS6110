/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Sourceable;

/**
 * @author zirkel
 * 
 */
public class CommonSourceable implements Sourceable {

	private CIVLSource source;

	public CommonSourceable(CIVLSource source) {
		this.source = source;
	}

	@Override
	public CIVLSource getSource() {
		return source;
	}

	@Override
	public void setCIVLSource(CIVLSource source) {
		this.source = source;
	}

}
