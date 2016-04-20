package edu.udel.cis.vsl.civl.gui.common;

import java.io.File;
import java.util.HashMap;
import javax.swing.tree.DefaultMutableTreeNode;

/**
 * This class is the container that hold all of the relevant data about a run
 * configuration. The GUI will take this information and save it to a file that
 * can later be parsed and ran.
 * 
 * @author noyes
 * 
 */
public class RunConfigDataNode extends DefaultMutableTreeNode {
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * The name of the <code>RunConfig</code>.
	 */
	private String name;

	/**
	 * The command type for this <code>RunConfig</code>.
	 */
	private CIVL_Command command;
	
	/**
	 * A hash map that stores each option with its value;
	 */
	private HashMap<String, Object> optValMap;

	/**
	 * The selected target <code>CIVL</code> file.
	 */
	private File selectedFile;
	
	/**
	 * The list of inputs for this Run Configuration.
	 */
	private CIVL_Input[] inputs;
	
	/**
	 * Marks whether the current runConfiguration should be saved to an XML file or not.
	 */
	private boolean toSave;
	
	/**
	 * Marks whether the current runConfiguration should be deleted or not.
	 */
	private boolean toDelete;

	public RunConfigDataNode(CIVL_Command command) {
		super();
		this.command = command;
		this.setToSave(false);
	}

	public File getSelectedFile() {
		return selectedFile;
	}

	public void setSelectedFile(File selectedFile) {
		this.selectedFile = selectedFile;
	}

	public CIVL_Command getCommand() {
		return command;
	}

	public void setCommand(CIVL_Command command) {
		this.command = command;
	}

	public String getName() {
		return name;
	}

	public void setName(String name) {
		this.name = name;
	}

	public boolean isToSave() {
		return toSave;
	}

	public void setToSave(boolean toSave) {
		this.toSave = toSave;
	}

	public HashMap<String, Object> getOptValMap() {
		return optValMap;
	}

	public void setOptValMap(HashMap<String, Object> optValMap) {
		this.optValMap = optValMap;
	}

	public CIVL_Input[] getInputs() {
		return inputs;
	}

	public void setInputs(CIVL_Input[] inputs) {
		this.inputs = inputs;
	}

	public boolean isToDelete() {
		return toDelete;
	}

	public void setToDelete(boolean toDelete) {
		this.toDelete = toDelete;
	}
}
