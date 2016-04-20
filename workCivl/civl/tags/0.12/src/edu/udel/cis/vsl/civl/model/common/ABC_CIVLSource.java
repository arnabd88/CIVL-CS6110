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

	/* ************************** Instance Fields ************************** */

	private Source abcSource;

	/* **************************** Constructors *************************** */

	public ABC_CIVLSource(Source abcSource) {
		this.abcSource = abcSource;
	}

	/* *********************** Methods from CIVLSource ********************* */

	@Override
	public String getLocation() {
		return abcSource.getLocation(true);
	}

	@Override
	public String getSummary() {
		return abcSource.getSummary(true);
	}

	@Override
	public void print(PrintStream out) {
		abcSource.print(out);
	}
	
//	@Override
//	public void printShorterFileNameMap(PrintStream out) {
//		abcSource.printShorterFileNameMap(out);
//	}

	/* ************************* Methods from Object *********************** */

	public String toString() {
		return abcSource.toString();
	}

	/* *************************** Public Methods ************************** */

	public Source getABCSource() {
		return abcSource;
	}

}
