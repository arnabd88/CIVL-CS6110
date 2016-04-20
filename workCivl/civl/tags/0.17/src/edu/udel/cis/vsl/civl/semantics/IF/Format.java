package edu.udel.cis.vsl.civl.semantics.IF;


public class Format {
	public enum ConversionType {
		INT, DOUBLE, CHAR, STRING, POINTER, VOID
	};

	public ConversionType type;
	public StringBuffer string;

	public Format(StringBuffer content, ConversionType conversion) {
		this.string = content;
		this.type = conversion;
	}

	@Override
	public String toString() {
		return this.string.toString();
	}
}
