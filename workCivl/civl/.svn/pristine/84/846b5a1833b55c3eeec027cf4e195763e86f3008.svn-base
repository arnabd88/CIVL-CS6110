package edu.udel.cis.vsl.civl.gui.common;

import javax.swing.JPanel;

import edu.udel.cis.vsl.gmc.Option;

/**
 * This class holds all necessary information that will be needed by the GUI in
 * order to construct different views for the various commands.
 * 
 * @author noyes
 * 
 */
public class CIVL_Command {
	/**
	 * The name of the <code>CIVL_Command</code>.
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
	 * A value that is true if inputs are need for this
	 * <code>CIVL_Command</code>, otherwise false.
	 */
	private boolean allowInputs;
	
	//TODO: change to some custom class possibly
	private JPanel view;
	//private JTabbedPane view;

	public CIVL_Command(String name, String description,
			Option[] allowedOptions, boolean allowInputs, JPanel view) {
		this.name = name;
		this.description = description;
		this.allowedOptions = allowedOptions;
		this.allowInputs = allowInputs;
		this.view = view;
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

	/**
	 * Gets the JTabbedPane view that will be displayed in the CIVL GUI.
	 * 
	 * @return
	 */
	public JPanel getView() { 
		return view;
	}

}
