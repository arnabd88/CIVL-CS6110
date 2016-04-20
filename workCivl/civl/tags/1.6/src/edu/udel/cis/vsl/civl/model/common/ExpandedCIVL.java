package edu.udel.cis.vsl.civl.model.common;

import java.io.PrintStream;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;

public class ExpandedCIVL implements CIVLSource {

	private CIVLSource expandedSource;
	private CIVLSource baseSource;

	public ExpandedCIVL(CIVLSource expanded, CIVLSource base) {
		this.expandedSource = expanded;
		this.baseSource = base;
	}

	@Override
	public void print(PrintStream out) {
		out.print(this.getSummary());
	}

	@Override
	public String getLocation() {
		return expandedSource.getLocation();
	}

	@Override
	public String getSummary() {
		return expandedSource.getSummary() + " from " + baseSource.getSummary();
	}

	@Override
	public boolean isSystemSource() {
		return false;
	}

	@Override
	public String getFileName() {
		return this.expandedSource.getFileName();
	}

	@Override
	public String getContent() {
		return expandedSource.getContent() + " from " + baseSource.getContent();
	}

}
