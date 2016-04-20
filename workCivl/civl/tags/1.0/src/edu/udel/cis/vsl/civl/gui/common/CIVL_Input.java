package edu.udel.cis.vsl.civl.gui.common;

public class CIVL_Input {
	private String name;
	private String type;
	private Object value;
	
	public CIVL_Input(String name, String type){
		this.setName(name);
		this.setType(type);
		setValue(null);
	}

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
}
