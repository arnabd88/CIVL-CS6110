package edu.udel.cis.vsl.abc.ast.conversion.IF;

import edu.udel.cis.vsl.abc.ast.type.IF.ObjectType;
import edu.udel.cis.vsl.abc.ast.type.IF.UnqualifiedObjectType;

/**
 * An Lvalue conversion, i.e., a conversion from the type of an lvalue to the
 * type of the value obtained by evaluating that lvalue. C11 Sec. 6.3.2.1 says:
 * 
 * <blockquote> Except when it is the operand of the <code>sizeof</code>
 * operator, the <code>_Alignof</code> operator, the unary <code>&</code>
 * operator, the <code>++</code> operator, the <code>--</code> operator, or the
 * left operand of the <code>.</code> operator or an assignment operator, an
 * lvalue that does not have array type is converted to the value stored in the
 * designated object (and is no longer an lvalue); this is called lvalue
 * conversion. If the lvalue has qualified type, the value has the unqualified
 * version of the type of the lvalue; additionally, if the lvalue has atomic
 * type, the value has the non-atomic version of the type of the lvalue;
 * otherwise, the value has the type of the lvalue. If the lvalue has an
 * incomplete type and does not have array type, the behavior is undefined. If
 * the lvalue designates an object of automatic storage duration that could have
 * been declared with the register storage class (never had its address taken),
 * and that object is uninitialized (not declared with an initializer and no
 * assignment to it has been performed prior to use), the behavior is undefined.
 * </blockquote>
 * 
 * @author siegel
 * 
 */
public interface LvalueConversion extends Conversion {

	@Override
	ObjectType getOldType();

	@Override
	UnqualifiedObjectType getNewType();

}
