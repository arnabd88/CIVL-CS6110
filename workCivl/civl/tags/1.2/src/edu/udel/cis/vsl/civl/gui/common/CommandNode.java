package edu.udel.cis.vsl.civl.gui.common;

import java.io.Serializable;

import javax.swing.tree.DefaultMutableTreeNode;

import edu.udel.cis.vsl.civl.run.IF.CommandLine.CommandName;
import edu.udel.cis.vsl.civl.run.common.NormalCommandLine.NormalCommandKind;

/**
 * This class is basic wrapper class that represents the node that corresponds to a certain command(RUN, SHOW etc.)
 * @author StevenNoyes
 *
 */
public class CommandNode extends DefaultMutableTreeNode implements Serializable {	
	/**
	 * The name of the Command.
	 */
	public CommandName commandName;
	
	public CommandNode(String name, CommandName comName){
		super(name);
		this.commandName = comName;
	}
}
