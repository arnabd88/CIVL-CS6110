package edu.udel.cis.vsl.civl.gui.common;

import java.awt.Component;

import javax.swing.AbstractCellEditor;
import javax.swing.JFormattedTextField;
import javax.swing.JTable;
import javax.swing.table.TableCellEditor;

/**
 * This editor class is used to override the default behavior for editing
 * numbers/Strings in a JTable. From a <code>JTextField</code> to a
 * <code>JFormattedTextField</code> with the appropriate format filters.
 * 
 * @author noyes
 * 
 */
public class FormattedTextFieldEditor extends AbstractCellEditor implements
		TableCellEditor {
	private static final long serialVersionUID = 1L;

	private JFormattedTextField jftf;

	public FormattedTextFieldEditor() {

	}

	@Override
	public Object getCellEditorValue() {
		return jftf.getText();
	}

	@Override
	public Component getTableCellEditorComponent(JTable table, Object value,
			boolean isSelected, int row, int column) {
		jftf = new JFormattedTextField(value);
		return jftf;
	}

}
