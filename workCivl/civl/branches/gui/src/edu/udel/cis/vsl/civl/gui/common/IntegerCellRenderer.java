package edu.udel.cis.vsl.civl.gui.common;

import java.awt.Component;

import javax.swing.JTable;
import javax.swing.table.TableCellRenderer;

/**
 * The TableCellRenderer for displaying Integers in the CIVL_Table.
 * @author StevenNoyes
 *
 */
public class IntegerCellRenderer implements TableCellRenderer {
	/**
	 * The component that will be rendered by the renderer.
	 */
	private IntegerPanel component;

	public IntegerCellRenderer() {
		component = new IntegerPanel();
	}

	@Override
	public Component getTableCellRendererComponent(JTable table, Object value,
			boolean isSelected, boolean isInit, int row, int column) {
		int selectedVal = (int) value;
		component.updateData(selectedVal, isSelected, table);
		return component;
	}
}
