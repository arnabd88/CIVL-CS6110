package edu.udel.cis.vsl.civl.model.common;

import java.io.PrintStream;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;

public class SystemCIVLSource implements CIVLSource {

	@Override
	public void print(PrintStream out) {
		out.print("CIVL System object");
	}

	@Override
	public String getLocation() {
		return "CIVL System object";
	}

	@Override
	public String getSummary() {
		return "CIVL System object";
	}

	@Override
	public void printShorterFileNameMap(PrintStream out) {

	}

}
