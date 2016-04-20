package edu.udel.cis.vsl.civl.gui.common;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.SortedMap;

import javax.swing.tree.DefaultMutableTreeNode;

import edu.udel.cis.vsl.civl.config.IF.CIVLConstants;
import edu.udel.cis.vsl.civl.run.IF.CommandLine;
import edu.udel.cis.vsl.civl.run.IF.CommandLine.CommandLineKind;
import edu.udel.cis.vsl.civl.run.common.CIVLCommand;
import edu.udel.cis.vsl.civl.run.common.NormalCommandLine;
import edu.udel.cis.vsl.civl.run.common.NormalCommandLine.NormalCommandKind;
import edu.udel.cis.vsl.gmc.GMCConfiguration;
import edu.udel.cis.vsl.gmc.Option;

/**
 * This class is the container that hold all of the relevant data about a run
 * configuration. The GUI will take this information and save it to a file that
 * can later be parsed and ran.
 * 
 * @author noyes
 * 
 */
public class RunConfigDataNode extends DefaultMutableTreeNode implements
		Serializable {
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * The name of the <code>RunConfig</code>.
	 */
	private String name;

	// TODO: erase this, we want multiple files not just one
	/**
	 * The selected target <code>CIVL</code> file.
	 */
	private File selectedFile;

	/**
	 * The selected target <code>CIVL</code> files.
	 */
	private ArrayList<File> selectedFiles;

	/**
	 * The list of input values for this Run Configuration.
	 */
	private ArrayList<CIVL_Input> inputs;

	/**
	 * Marks whether unsaved changes have been made to the RunConfigDataNode.
	 */
	private boolean changed;

	/**
	 * An array that stores all of the Option values
	 */
	private Object[] values;

	/**
	 * A GMC config that is needed for the file
	 */
	private GMCConfiguration gmcConfig;

	/**
	 * Is this RunConfigDataNode brand new?(true) Has it been modified in any
	 * way?(false)
	 */
	private boolean brandNew;

	/**
	 * The directory to which the RunConfigDataNode is serialized to.
	 */
	private String serializeDestination;

	/**
	 * The NormalCommandKind associated with this RunConfigurationDataNode
	 */

	public CommandLine comLine;

	/**
	 * A boolean denoting whether a RunConfigurationDataNode is to be deleted or
	 * not.
	 */
	private boolean markedForDelete;

	/**
	 * Whether or not the apply button has been clicked.
	 */
	public boolean applyClicked;

	// TODO: figure out use for this
	public boolean tableChanged;

	public RunConfigDataNode(CommandLine comLine) {
		this.applyClicked = false;
		@SuppressWarnings("unused")
		SortedMap<String, Option> map = null;
		this.selectedFiles = new ArrayList<File>();
		this.inputs = new ArrayList<CIVL_Input>();
		this.markedForDelete = false;
		GMCConfiguration c = new GMCConfiguration(Arrays.asList(CIVLConstants
				.getAllOptions()));

		if (comLine == null) {
		}

		else if (comLine.commandLineKind() == CommandLineKind.COMPARE) {
			map = CIVLCommand.getVerifyOrCompareOptions();
			// c = new GMCConfiguration(map.values());
		}

		else if (comLine.commandLineKind() == CommandLineKind.NORMAL) {
			NormalCommandKind commandKind = ((NormalCommandLine) comLine)
					.normalCommandKind();
			if (commandKind.equals(NormalCommandKind.RUN)) {
				map = CIVLCommand.getRunOptions();
				// c = new GMCConfiguration(map.values());
			}

			else if (commandKind.equals(NormalCommandKind.VERIFY)) {
				map = CIVLCommand.getVerifyOrCompareOptions();
				// c = new GMCConfiguration(map.values());
			}

			else if (commandKind.equals(NormalCommandKind.SHOW)) {
				map = CIVLCommand.getShowOptions();
				// c = new GMCConfiguration(map.values());
			}
		}
		this.setGmcConfig(c);

		int size = CIVLConstants.getAllOptions().length;
		this.setValues(new Object[size]); // DEPRECIATED
		this.setChanged(false);
		this.brandNew = true;
		this.tableChanged = false;
		this.comLine = comLine;
	}

	/**
	 * Returns the command type of a CommandLine object that is NORMAL. Returns
	 * null if the CommandLine command kind object isn't NORMAL
	 * 
	 * @return The NormalCommandKind of the CommandLine
	 */
	public NormalCommandKind getNormalCommandKind() {
		if (comLine.commandLineKind() == CommandLineKind.NORMAL) {
			return ((NormalCommandLine) comLine).normalCommandKind();
		} else
			return null;
	}

	/*
	 * public CommandKind getCompareCommandKind() { if
	 * (comLine.commandLineKind()==CommandLineKind.COMPARE) { return
	 * CommandLine.COMPARE; } else return null; }
	 */

	/**
	 * Serializes the RunConfigDataNode so that it can be accessed later.
	 */
	public void serialize() {
		try {
			FileOutputStream fileOut = new FileOutputStream(
					serializeDestination + "/" + name);
			ObjectOutputStream out = new ObjectOutputStream(fileOut);
			out.writeObject(this);
			out.close();
			fileOut.close();
			System.out.println("Serialized data is saved in "
					+ serializeDestination);
		} catch (IOException i) {
			i.printStackTrace();
		}
	}

	/**
	 * Deserializes the RunConfigurationDataNode and returns the associated
	 * object
	 * 
	 * @return The RunConfigurationDataNode from the ObjectStream
	 */
	public RunConfigDataNode deserialize() {
		RunConfigDataNode config = null;
		try {
			FileInputStream fileIn = new FileInputStream(serializeDestination
					+ "/" + name);
			ObjectInputStream in = new ObjectInputStream(fileIn);
			config = (RunConfigDataNode) in.readObject();
			System.out.println(config.getNormalCommandKind());
			in.close();
			fileIn.close();
			if (!config.isMarkedForDelete()) {
				System.out.println("Deserialized RunConfig...");
				System.out.println("Name: " + config.name);
				for (int i = 0; i < config.getSelectedFiles().size(); i++) {
					System.out.println("File: "
							+ config.getSelectedFiles().get(i));
				}
			}
			return config;

		} catch (IOException i) {
			i.printStackTrace();
			return null;
		} catch (ClassNotFoundException c) {
			System.out.println("RunConfigDataNode class not found");
			c.printStackTrace();
			return null;
		}
	}

	/**
	 * Marks the RunConfigurationDataNode for delete
	 */
	public void deleteConfig() {
		this.markedForDelete = true;
	}

	/*
	 * Getters & Setters
	 */

	public boolean isMarkedForDelete() {
		return markedForDelete;
	}

	public File getSelectedFile() {
		return selectedFile;
	}

	public void setSelectedFile(File selectedFile) {
		this.selectedFile = selectedFile;
	}

	public ArrayList<File> getSelectedFiles() {
		return selectedFiles;
	}

	public void setSelectedFiles(ArrayList<File> selectedFiles) {
		this.selectedFiles = selectedFiles;
	}

	public String getName() {
		return name;
	}

	public void setName(String name) {
		this.name = name;
	}

	public boolean isChanged() {
		return changed;
	}

	public void setChanged(boolean changed) {
		this.changed = changed;
	}

	public ArrayList<CIVL_Input> getInputs() {
		return inputs;
	}

	public void setInputs(ArrayList<CIVL_Input> inputs) {
		this.inputs = inputs;
	}

	public Object[] getValues() {
		return values;
	}

	public void setValues(Object[] values) {
		this.values = values;
	}

	public boolean isBrandNew() {
		return brandNew;
	}

	public void setBrandNew(boolean brandNew) {
		this.brandNew = brandNew;

	}

	public String getSerializeDestination() {
		return serializeDestination;
	}

	public void setSerializeDestination(String serializeDestination) {
		this.serializeDestination = serializeDestination;
	}

	public GMCConfiguration getGmcConfig() {
		return gmcConfig;
	}

	public void setGmcConfig(GMCConfiguration gmcConfig) {
		this.gmcConfig = gmcConfig;
	}
}
