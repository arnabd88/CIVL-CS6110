package edu.udel.cis.vsl.civl.gui.common;

import java.awt.Component;

import javax.swing.AbstractCellEditor;
import javax.swing.JTable;
import javax.swing.table.TableCellEditor;

/**
 * The TableCellEditor for displaying Integers in the CIVL_Table.
 * @author StevenNoyes
 *
 */
public class IntegerCellEditor extends AbstractCellEditor implements
		TableCellEditor {
	private static final long serialVersionUID = 1L;
	/**
	 * The component that will be edited by the editor.
	 */
	private IntegerPanel component;

	public IntegerCellEditor() {
		component = new IntegerPanel();
	}

	@Override
	public Component getTableCellEditorComponent(JTable table, Object value,
			boolean isSelected, int row, int column) {
		int selectedVal = (int) value;
		component.updateData(selectedVal, true, table);
		return component;
	}

	@Override
	public Object getCellEditorValue() {
		return component.getVal();
	}
}