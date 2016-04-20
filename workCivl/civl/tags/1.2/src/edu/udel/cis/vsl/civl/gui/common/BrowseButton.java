package edu.udel.cis.vsl.civl.gui.common;

import java.awt.event.ActionEvent;

import javax.swing.AbstractAction;
import javax.swing.JButton;

/**
 * The BrowseButton will add files to the Browse File table in the GUI. It will
 * only be located in the CIVL Table. All other buttons that say "Browse..." and
 * aren't in a CIVL Table, are NOT a BrowseButton.
 * 
 * @author StevenNoyes
 *
 */
public class BrowseButton extends JButton {

	/**
	 * 
	 */
	private static final long serialVersionUID = -2502288298798352255L;

	/**
	 * The action that the button will perform
	 */
	private AbstractAction act;

	/**
	 * The PathChooser Object that will launch from this button
	 */
	private PathChooser pc;

	/**
	 * The String representing the path that is gotten from the pc
	 */
	private String pathString;

	/**
	 * The name of the Option repesented as a String
	 */
	public String optName;

	/**
	 * The parent GUI of this button
	 */
	private GUI_revamp parent;

	public BrowseButton(String name, GUI_revamp parent) {
		super(name);
		this.optName = name;
		this.parent = parent;
		setPathString("");
		initAction();
	}

	/**
	 * Creates the action that will launch the small PathChooser GUI
	 */
	private void initAction() {
		act = new AbstractAction() {
			private static final long serialVersionUID = 1L;

			public void actionPerformed(ActionEvent e) {
				pc = new PathChooser(pathString, optName, parent);
				setPathString(pc.format());
				// System.out.println(pathString);
				repaint();
			}
		};
		this.setAction(act);
	}

	public String getPathString() {
		return pathString;
	}

	public void setPathString(String pathString) {
		this.pathString = pathString;
	}
}
