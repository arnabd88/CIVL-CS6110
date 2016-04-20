package edu.udel.cis.vsl.civl.gui.common;

import java.awt.Component;

import javax.swing.AbstractCellEditor;
import javax.swing.JTable;
import javax.swing.table.TableCellEditor;

/**
 * This editor class is used to override the default behavior for rendering a
 * boolean value in a JTable. From a JCheckBox(default) to a JPanel consisting
 * of the boolean values true and false(As JRadioButtons).
 * 
 * @author noyes
 * 
 */
public class BooleanCellEditor extends AbstractCellEditor implements
		TableCellEditor {
	/**
	 * required by eclipse
	 */
	private static final long serialVersionUID = 1L;
	/**
	 * The component that will be edited by the editor.
	 */
	private RadioPanel component;

	public BooleanCellEditor() {
		component = new RadioPanel();
	}
	
	@Override
	public Component getTableCellEditorComponent(JTable table, Object value,
			boolean isSelected, int row, int column) {
		Boolean selectedVal = (Boolean) value;
		component.updateData(selectedVal, true, table);
		return component;
	}

	@Override
	public Object getCellEditorValue() {
		return component.selectedVal;
	}
}
