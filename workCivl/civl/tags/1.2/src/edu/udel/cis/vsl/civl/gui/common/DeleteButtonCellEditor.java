package edu.udel.cis.vsl.civl.gui.common;

import java.awt.Component;

import javax.swing.AbstractCellEditor;
import javax.swing.JButton;
import javax.swing.JTable;
import javax.swing.table.TableCellEditor;

/**
 * The TableCellEditor for the DeleteButton in the CIVL_Table.
 * @author StevenNoyes
 *
 */
public class DeleteButtonCellEditor extends AbstractCellEditor implements TableCellEditor {
	private static final long serialVersionUID = 1L;
	/**
	 * The component that will be edited by the editor.
	 */
	private JButton component;

	public DeleteButtonCellEditor(CIVLTable table) {
		component =  new DeleteButton(table);
		component.setText("Delete");
	}
	
	@Override
	public Component getTableCellEditorComponent(JTable table, Object value,
			boolean isSelected, int row, int column) {
		
		return component;
	}

	@Override
	public Object getCellEditorValue() {
		return "Delete";
	}	
}
