package edu.udel.cis.vsl.civl.gui.common;

import java.io.Serializable;

import edu.udel.cis.vsl.gmc.Option;

/**
 * This class holds all necessary information that will be needed by the GUI in
 * order to construct different views for the various commands.
 * 
 * @author noyes
 * 
 */
public class CIVL_Command implements Serializable{
	/**
	 * 
	 */
	private static final long serialVersionUID = 5086253399276183984L;

	/**
	 * The name of this {@link CIVL_Command}.
	 */
	private String name;

	/**
	 * The description associated with this <code>CIVL_Command</code>.
	 */
	private String description;

	/**
	 * The options that can be enabled for this <code>CIVL_Command</code>.
	 */
	private Option[] allowedOptions;

	/**
	 * A value that is true if inputs are needed for this
	 * <code>CIVL_Command</code>, otherwise false.
	 */
	private boolean allowInputs;
	
	/**
	 * Constructs a new CIVL_Command.
	 * @param name 
	 * @param description
	 * @param allowedOptions
	 * @param allowInputs
	 */
	//TODO: finish documentation
	public CIVL_Command(String name, String description,
			Option[] allowedOptions, boolean allowInputs) {
		this.name = name;
		this.description = description;
		this.allowedOptions = allowedOptions;
		this.allowInputs = allowInputs;
	}

	/**
	 * Gets the name.
	 * 
	 * @return The name
	 */
	public String getName() {
		return name;
	}

	/**
	 * Gets the description.
	 * 
	 * @return The description
	 */
	public String getDescription() {
		return description;
	}

	/**
	 * Gets the allowed options.
	 * 
	 * @return The allowed options
	 */
	public Option[] getAllowedOptions() {
		return allowedOptions;
	}

	/**
	 * Gets the allowInputs boolean.
	 * 
	 * @return The value for allowInputs
	 */
	public boolean isAllowInputs() {
		return allowInputs;
	}

}
