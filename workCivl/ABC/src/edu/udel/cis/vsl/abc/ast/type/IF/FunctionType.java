package edu.udel.cis.vsl.abc.ast.type.IF;

import edu.udel.cis.vsl.abc.ast.IF.ASTException;

/**
 * According to C11, a function type is characterized by the return type and the
 * number and types of the arguments. In reality, it is also necessary to know
 * whether the type was generated from an identifier list or a parameter type
 * list, as certain concepts (e.g., "compatibility") depend on this information.
 * 
 * If fromIdentifierList is true and parametersKnown is false, this type came
 * from a non-definition declaration of the form "f()", so no information about
 * the arguments is known.
 * 
 * If fromIdentifierList is false, then parametersKnown must be true, as this
 * type came from a parameter-type list which must necessarily specify all of
 * the parameter types.
 * 
 * A declaration of the form "f(void)" yields a type with fromIdentifierList
 * false, parametersKnown true, and parameterTypes of length 0. A
 * declaration-definition of the form "f() {...}" yields a type with
 * fromIdentifierList true, parametersKnown true, and parameterTypes of length
 * 0. As stated above, a declaration of the form "f()" which is not part of a
 * definition yields a type with fromIdentifierList true and parametersKnown
 * false.
 * 
 * @author siegel
 * 
 */
public interface FunctionType extends Type {

	/**
	 * The return type of this function. Non-null.
	 * 
	 * @return the return type
	 */
	ObjectType getReturnType();

	/**
	 * Was this type generated from an identifier list (as opposed to a
	 * parameter type list)?
	 * 
	 * @return true iff type was generated from an identifier list
	 */
	boolean fromIdentifierList();

	/**
	 * Returns true iff the parameter information for this function type is
	 * known.
	 * 
	 * @return true iff parameter information is known
	 */
	boolean parametersKnown();

	/**
	 * Returns the number of parameters.
	 * 
	 * @exception ASTException
	 *                if the parameter information is not known
	 * 
	 * @return the number of parameters
	 */
	int getNumParameters() throws ASTException;

	/**
	 * Returns the type of the index-th parameter.
	 * 
	 * @param index
	 *            integer in range [0,n-1], where n is the number of parameters
	 * 
	 * @exception ASTException
	 *                if the parameter information is not known
	 * @return the index-th parameter type
	 */
	ObjectType getParameterType(int index);

	/**
	 * The sequence of formal parameter declarations for this function type. An
	 * identifier list is represented by a sequence of declarations in which all
	 * components other than the identifiers are null.
	 * 
	 * @exception ASTException
	 *                if the parameter information is not known
	 * @return sequence of parameter declarations
	 */
	Iterable<ObjectType> getParameterTypes();

	/**
	 * A function that takes a variable number of arguments will have an
	 * ellipsis occur at the end of its argument list.
	 * 
	 * @exception RuntimeException
	 *                if the parameter information is not known
	 * 
	 * @return true iff this function takes a variable number of arguments
	 */
	boolean hasVariableArgs();

}
