package edu.udel.cis.vsl.civl.gui.common;

import java.awt.Component;
import javax.swing.JTable;
import javax.swing.table.TableCellRenderer;

/**
 * This renderer class is used to override the default behavior for rendering a
 * boolean value in a JTable. From a JCheckBox(default) to a JPanel consisting
 * of the boolean values true and false(As JRadioButtons).
 * 
 * @author noyes
 * 
 */
public class BooleanCellRenderer implements TableCellRenderer {
	/**
	 * The component that will be rendered by the renderer.
	 */
	private RadioPanel component;

	public BooleanCellRenderer() {
		component = new RadioPanel();
	}

	@Override
	public Component getTableCellRendererComponent(JTable table, Object value,
			boolean isSelected, boolean isInit, int row, int column) {
		Boolean selectedVal = (Boolean) value;

		component.updateData(selectedVal, isSelected, table);
		return component;
	}
}
