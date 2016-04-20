package edu.udel.cis.vsl.civl.gui.common;

import java.awt.event.ActionEvent;

import javax.swing.AbstractAction;
import javax.swing.JButton;
import javax.swing.table.DefaultTableModel;

/**
 * The DeleteButton will delete files out of the Browse File Table.
 * 
 * @author StevenNoyes
 *
 */
public class DeleteButton extends JButton { 
	private static final long serialVersionUID = 1L;

	/**
	 * The action that the button will perform
	 */
	private AbstractAction act;
			
	/**
	 * The table this button is in.
	 */
	private CIVLTable table;
	
	public DeleteButton(CIVLTable table){
		setTable(table);
		initAction();
	}
	
	/**
	 * Creates the Action that will delete files out of the Browse File Table
	 */
	private void initAction(){
		act = new AbstractAction() {
			private static final long serialVersionUID = 1L;

			public void actionPerformed(ActionEvent e) {
				table.deleting = true;
				final DefaultTableModel currFileModel = (DefaultTableModel) table.getModel();
				int modelRow = table.getSelectedRow();
				
				if(modelRow != -1)
					currFileModel.removeRow(modelRow);
				
				table.deleting = false;
				repaint();
			}
		};
		this.setAction(act);
	}
	
	/*
	 * Getters & Setters
	 */

	public CIVLTable getTable() {
		return table;
	}

	public void setTable(CIVLTable table) {
		this.table = table;
	}
}