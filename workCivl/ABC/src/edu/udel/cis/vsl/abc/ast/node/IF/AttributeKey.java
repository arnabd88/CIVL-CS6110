package edu.udel.cis.vsl.abc.ast.node.IF;

/**
 * A key to be used as a key-attribute pair. This is used to associate
 * information of any kind to AST nodes.
 * 
 * Each attribute key has a name. Two different attribute keys can have the same
 * name. They are only equal if they are the same object.
 * 
 * Each attribute key has a class. This is type to which every attribute value
 * must belong.
 * 
 * @author siegel
 * 
 */
public interface AttributeKey {

	/**
	 * Returns the name of this attribute.
	 * 
	 * @return the name of the attribute
	 */
	String getAttributeName();

	/**
	 * Returns the class of this attribute. This is the type to which every
	 * attribute value associated to this key must belong.
	 * 
	 * @return the attribute class
	 */
	Class<? extends Object> getAttributeClass();

}
