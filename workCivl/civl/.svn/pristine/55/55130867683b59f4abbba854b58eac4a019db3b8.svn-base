package edu.udel.cis.vsl.civl.gui.common;

import java.io.Serializable;

import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.InitializerNode;

/**
 * A class that was created in order to store the necessar information that
 * described an input to a CIVL program.
 * 
 * @author StevenNoyes
 * 
 */
public class CIVL_Input implements Serializable {
	private static final long serialVersionUID = -1017486336799923756L;

	/**
	 * The name of the input.
	 */
	private String name;

	/**
	 * The type of the input represented as a string.
	 */
	private String type;

	/**
	 * The value of the input as an Object.
	 */
	private Object value;

	/**
	 * The Initializer associated with the input represented as a String.
	 */
	private String initializer;

	public CIVL_Input(String name, String type) {
		this.setName(name);
		this.setType(type);
		setValue(null);
		setInitializer("");
	}
	
	/*
	 * Getters & Setters 
	 */
	
	public String getName() {
		return name;
	}

	public void setName(String name) {
		this.name = name;
	}

	public String getType() {
		return type;
	}

	public void setType(String type) {
		this.type = type;
	}

	public Object getValue() {
		return value;
	}

	public void setValue(Object value) {
		this.value = value;
	}

	public String getInitializer() {
		return initializer;
	}

	public void setInitializer(String initializer) {
		this.initializer = initializer;
	}
}
