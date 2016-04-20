package edu.udel.cis.vsl.civl.gui.common;

import java.awt.Component;

import javax.swing.AbstractCellEditor;
import javax.swing.ButtonGroup;
import javax.swing.JPanel;
import javax.swing.JRadioButton;
import javax.swing.JTable;
import javax.swing.table.TableCellEditor;
import javax.swing.table.TableCellRenderer;

public class RadioPanelCell extends AbstractCellEditor implements TableCellEditor, TableCellRenderer{
	private static final long serialVersionUID = 1L;
	
	private JRadioButton rb_true;
	private JRadioButton rb_false;
	private ButtonGroup group;
	private JPanel radioPanel;
	private boolean selectedVal;
	
	public RadioPanelCell() {
		radioPanel = new JPanel();
		rb_true = new JRadioButton("true", true);
		rb_false = new JRadioButton("false", false);
		group = new ButtonGroup();		
		
		group.add(rb_true);
		group.add(rb_false);

		radioPanel.add(rb_true);
		radioPanel.add(rb_false);
	}
	
	public void updateData(Boolean selectedVal, boolean isSelected, JTable table) {
		this.selectedVal = selectedVal;

		if (isSelected) {
			radioPanel.setBackground(table.getSelectionBackground());
			
		} else {
			radioPanel.setBackground(table.getSelectionForeground());
		}
		
		if (selectedVal)
			rb_true.setSelected(true);
		else if (!selectedVal)
			rb_false.setSelected(true);
	}
	
	@Override
	public Component getTableCellEditorComponent(JTable table, Object value,
			boolean isSelected, int row, int column) {
		Boolean selectedVal = (Boolean) value;
		updateData(selectedVal, true, table);
		
		return radioPanel;
	}
	
	@Override
	public Component getTableCellRendererComponent(JTable table, Object value,
			boolean isSelected, boolean hasFocus, int row, int column) {
		Boolean selectedVal = (Boolean) value;

		updateData(selectedVal, isSelected, table);
		
		return radioPanel;
	}
	
	@Override
	public Object getCellEditorValue() {
		return selectedVal;
	}

	
}
