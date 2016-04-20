package edu.udel.cis.vsl.civl.gui.common;

import java.awt.event.ItemEvent;
import java.awt.event.ItemListener;

import javax.swing.ButtonGroup;
import javax.swing.JPanel;
import javax.swing.JRadioButton;
import javax.swing.JTable;

/**
 * A custom JPanel that contains radio buttons for true & false. It will be used
 * as the component that will override JCheckBox when a Boolean vlaue is passed
 * into a CIVL_Table(JTable).
 * 
 * @author noyes
 * 
 */
public class RadioPanel extends JPanel {
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * The radio button for True.
	 */
	private JRadioButton rb_true;

	/**
	 * The radio button for False.
	 */
	private JRadioButton rb_false;

	/**
	 * The <code>ButtonGroup</code> that the radio buttons will be placed in.
	 */
	private ButtonGroup group;

	/**
	 * The currently selected value(it can only be a Boolean).
	 */
	public Boolean selectedVal;

	public RadioPanel() {
		rb_true = new JRadioButton("true", true);
		rb_false = new JRadioButton("false", false);

		rb_true.addItemListener(new ItemListener() {

			@Override
			public void itemStateChanged(ItemEvent e) {
				if (e.getStateChange() == ItemEvent.SELECTED) {
					selectedVal = true;
				}
			}
		});

		rb_false.addItemListener(new ItemListener() {

			@Override
			public void itemStateChanged(ItemEvent e) {
				if (e.getStateChange() == ItemEvent.SELECTED) {
					selectedVal = false;
				}
			}
		});

		group = new ButtonGroup();
		group.add(rb_true);
		group.add(rb_false);

		add(rb_true);
		add(rb_false);
	}

	/**
	 * Updates the data contained in this <code>RadioPanel</code>.
	 * 
	 * @param selectedVal
	 *            The newly selected value.
	 * @param isSelected
	 *            Is the component selected?
	 * @param table
	 *            The table that we are updating data in.
	 */
	public void updateData(Boolean selectedVal, boolean isSelected, JTable table) {
		this.selectedVal = selectedVal;

		if (isSelected) {
			setBackground(table.getSelectionBackground());
		} else {
			setBackground(table.getSelectionForeground());
		}

		if (selectedVal) {
			rb_true.setSelected(true);
		} else if (!selectedVal) {
			rb_false.setSelected(true);
		}
	}
}
