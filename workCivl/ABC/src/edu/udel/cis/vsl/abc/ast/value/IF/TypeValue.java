package edu.udel.cis.vsl.abc.ast.value.IF;

import edu.udel.cis.vsl.abc.ast.type.IF.Type;

/**
 * A value which is a function of a type, such as "sizeof(type)" or
 * "_Alignof(type)".
 * 
 * Note that the "type" above is different from the type of this value, which is
 * typically an integer type.
 * 
 * @author siegel
 * 
 */
public interface TypeValue extends Value {

	public enum TypeValueKind {
		SIZEOF, ALIGNOF
	}

	Type getTypeArgument();
	
	TypeValueKind getTypeValueKind();

}
