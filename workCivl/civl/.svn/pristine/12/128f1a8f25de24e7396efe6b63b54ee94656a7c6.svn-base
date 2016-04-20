package edu.udel.cis.vsl.civl.gui.common;

import java.awt.Component;
import java.text.ParseException;

import javax.swing.InputVerifier;
import javax.swing.JComponent;
import javax.swing.JFormattedTextField;
import javax.swing.JFormattedTextField.AbstractFormatter;
import javax.swing.JTable;
import javax.swing.table.TableCellRenderer;

/**
 * This renderer class is used to override the default behavior for rendering
 * numbers/Strings in a JTable. From a <code>JTextField</code> to a
 * <code>JFormattedTextField</code> with the appropriate format filters.
 * 
 * @author noyes
 * 
 */
public class FormattedTextFieldRenderer implements TableCellRenderer {
	
	/**
	 * Verifies whether an input is of the correct format(Number, String etc.)
	 * @author StevenNoyes
	 *
	 */
	private class FormattedTextFieldVerifier extends InputVerifier {
		public boolean verify(JComponent input) {
			if (input instanceof JFormattedTextField) {
				JFormattedTextField ftf = (JFormattedTextField) input;
				AbstractFormatter formatter = ftf.getFormatter();
				if (formatter != null) {
					String text = ftf.getText();
					try {
						formatter.stringToValue(text);
						return true;
					} catch (ParseException pe) {
						return false;
					}
				}
			}
			return true;
		}

		public boolean shouldYieldFocus(JComponent input) {
			return verify(input);
		}
	}
	
	/**
	 * The text field associated with this Editor.
	 */
	private JFormattedTextField jftf;
	
	private String mode;
	
	/**
	 * The verifier associated with this Renderer
	 */
	//TODO: Make this actually work, there is somekind of bug that causes this not to work very well.
	private FormattedTextFieldVerifier verifier;

	public FormattedTextFieldRenderer() {
		super();
		verifier = new FormattedTextFieldVerifier();
		mode = "";
	}

	@Override
	public Component getTableCellRendererComponent(JTable table, Object value,
			boolean isSelected, boolean hasFocus, int row, int column) {
		jftf = new JFormattedTextField(value);
		jftf.setFocusLostBehavior(JFormattedTextField.REVERT);

		// not this, though.
		check();
		return jftf;
	}

	public String getMode() {
		return mode;
	}

	public void setMode(String mode) {
		this.mode = mode;
		// verifier.verify(jftf);
		// checkMode();
	}

	// doesnt do anything yet
	public void check() {
		// verifier.verify(jftf);
	}

}
