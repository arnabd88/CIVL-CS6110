package edu.udel.cis.vsl.abc.ast.type.common;

import java.io.PrintStream;

/**
 * An integer type represented only by a name, signedness, and possibly other
 * data. Concrete information about most aspects of the type is not necessarily
 * known, such as its size, conversion rank, and so on. It is used primarily to
 * represent integer types that are guaranteed to be defined in the Standard,
 * but for which the definitions are largely up to the implementation. Examples
 * include size_t, wchar_t, and so on.
 * 
 * This is analogous to a "symbolic constant" in symbolic execution.
 * 
 * Two instances of this class are considered equal iff they are ==. I.e., any
 * two distinct instances are considered to represent two different types, even
 * if they have the same name and signedness.
 * 
 * An instance of this class is not compatible with any other type (other than
 * itself). Note that this may be more strict than what actually happens in a C
 * implementation. (For example, if size_t is defined by a typedef to be long,
 * size_t will be compatible with long).
 * 
 * @author siegel
 * 
 */
public class SymbolicIntegerType extends CommonIntegerType {

	private String name;

	public SymbolicIntegerType(String name) {
		super(TypeKind.OTHER_INTEGER);
		this.name = name;
	}

	@Override
	public boolean isEnumeration() {
		return false;
	}

	@Override
	public void print(String prefix, PrintStream out, boolean abbrv) {
		out.print(name);
	}
}
