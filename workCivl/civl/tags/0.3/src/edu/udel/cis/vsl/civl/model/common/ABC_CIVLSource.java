package edu.udel.cis.vsl.civl.model.common;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;

/**
 * Implementation of CIVLSource formed by wrapping an ABC Source object.
 * 
 * @author siegel
 * 
 */
public class ABC_CIVLSource implements CIVLSource {

	private Source abcSource;

	public ABC_CIVLSource(Source abcSource) {
		this.abcSource = abcSource;
	}

	@Override
	public void print(PrintStream out) {
		abcSource.print(out);
	}

	@Override
	public String getLocation() {
		return abcSource.getLocation();
	}

	@Override
	public String getSummary() {
		return abcSource.getSummary();
	}

	public Source getABCSource() {
		return abcSource;
	}
	
	public String toString() {
		return abcSource.toString();
	}

}
