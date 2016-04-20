package edu.udel.cis.vsl.civl.gui.common;

import java.awt.Component;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;

import javax.swing.JButton;
import javax.swing.JTable;
import javax.swing.JTextArea;
import javax.swing.event.EventListenerList;
import javax.swing.table.TableCellEditor;
import javax.swing.table.TableCellRenderer;

import edu.udel.cis.vsl.gmc.Option;

/**
 * This class is used to ensure that the first column of the
 * <code>CIVLTable</code>(JTable) is not editable, as we do not want users to be
 * able to change the option names in the table where selected options are
 * displayed. In addition to this, it contains a custom cell renderer and a
 * custom cell editor to override undesirable JTable behavior.
 * 
 * @author noyes
 * 
 */
public class CIVLTable extends JTable implements MouseListener {
	/**
	 * 
	 */
	private static final long serialVersionUID = -5345179673948036576L;

	/**
	 * The custom renderer to be used for cells that have a boolean value.
	 */
	private BooleanCellRenderer boolean_render;

	/**
	 * The custom editor to be used for cells that have a boolean value.
	 */
	private BooleanCellEditor boolean_edit;

	/**
	 * A renderer used to render Strings and Numbers.
	 */
	private FormattedTextFieldRenderer text_render;

	/**
	 * An editor used to edit Strings and Numbers.
	 */
	private FormattedTextFieldEditor text_edit;

	/**
	 * The columns that can be edited in an instance of a
	 * <code>CIVL_Table</code>.
	 */
	private int[] editableCols;

	/**
	 * The type of table stored as a String. The supported types currently are:
	 * <li>"option" for the option tables in the GUI</li> <li>"input" for the
	 * input tables in the GUI</li>
	 */
	private String tableType;

	/**
	 * The renderer for option values.
	 */
	private OptionCellRenderer option_render;

	/**
	 * The list of EventListeners
	 */
	protected EventListenerList listenerList = new EventListenerList();

	/**
	 * The JButton editors that will be used to render the browse file button
	 * for the include path options.
	 */
	private BrowseButtonCellEditor browsePathSys_edit;
	private BrowseButtonCellEditor browsePathUser_edit;

	/**
	 * The JButton renderers that will be used to render the browse file button
	 * for the include path options.
	 */
	private BrowseButtonCellRenderer browsePathSys_render;
	private BrowseButtonCellRenderer browsePathUser_render;

	/**
	 * The JButton renderer that will be used for the delete(file out of a file
	 * table) button.
	 */
	private DeleteButtonCellRenderer deleteButton_render;

	/**
	 * The JButton editor that will be used for the delete(file out of a file
	 * table) button.
	 */
	private DeleteButtonCellEditor deleteButton_edit;

	private IntegerCellRenderer integer_render;

	private IntegerCellEditor integer_edit;

	/**
	 * True if the user is deleting a file, otherwise False.
	 */
	public boolean deleting;

	/**
	 * This custom class renders option values as option.name() in uneditable
	 * JTextAreas.
	 * 
	 * @author noyes
	 * 
	 */
	private class OptionCellRenderer implements TableCellRenderer {
		private Option option;

		@Override
		public Component getTableCellRendererComponent(JTable table,
				Object value, boolean isSelected, boolean hasFocus, int row,
				int column) {
			return new JTextArea(option.name());
		}

	}

	CIVLTable(int[] editableCols, String tableType, GUI_revamp parent) {
		super();
		deleting = false;
		boolean_render = new BooleanCellRenderer();
		boolean_edit = new BooleanCellEditor();
		option_render = new OptionCellRenderer();
		text_render = new FormattedTextFieldRenderer();
		text_edit = new FormattedTextFieldEditor();
		browsePathSys_render = new BrowseButtonCellRenderer("sysIncludePath",
				parent);
		browsePathSys_edit = new BrowseButtonCellEditor("sysIncludePath",
				parent);
		browsePathUser_render = new BrowseButtonCellRenderer("userIncludePath",
				parent);
		browsePathUser_edit = new BrowseButtonCellEditor("userIncludePath",
				parent);
		deleteButton_render = new DeleteButtonCellRenderer(this);
		deleteButton_edit = new DeleteButtonCellEditor(this);
		integer_edit = new IntegerCellEditor();
		integer_render = new IntegerCellRenderer();

		this.editableCols = editableCols;
		this.tableType = tableType;
		this.addMouseListener(this);
	}

	/**
	 * Gets the <code>CIVL_Table</code>'s cell editor for a specific cell.
	 * 
	 * @param row
	 *            The row of the cell.
	 * @param col
	 *            The column of the cell.
	 * 
	 * @return The specified <code>TableCellEditor</code>
	 */
	public TableCellEditor getCellEditor(int row, int column) {
		Object value = super.getValueAt(row, column);
		Option opt = null;

		if (this.tableType.equals("option")) {
			opt = (Option) super.getValueAt(row, 0);
		}

		if (opt != null) {
			if (opt.name().equals("sysIncludePath")) {
				return browsePathSys_edit;
			}

			else if (opt.name().equals("userIncludePath")) {
				return browsePathUser_edit;
			}
		}

		if (value == null)
			value = "";

		if (tableType.equals("file") && value instanceof String) {
			if (value.equals("Delete")) {
				return deleteButton_edit;
			}
		}

		else if (value instanceof DeleteButtonCellEditor) {
			return deleteButton_edit;
		}

		else if (value instanceof Integer)
			return integer_edit;

		else if (value instanceof String && column != 0 && column != 2) {
			if (value.equals("sysIncludePath"))
				return browsePathSys_edit;

			else if (value.equals("userIncludePath"))
				return browsePathUser_edit;
		}

		// only for option table
		else if (value instanceof String && column == 1
				&& tableType == "option") {
			return text_edit;
		}

		else if (value instanceof Boolean)
			return boolean_edit;

		return super.getCellEditor(row, column);
	}

	/**
	 * Gets the <code>CIVL_Table</code>'s cell renderer for a specific cell.
	 * 
	 * @param row
	 *            The row of the cell.
	 * @param col
	 *            The column of the cell.
	 * 
	 * @return The specified <code>TableCellRenderer</code>
	 */
	public TableCellRenderer getCellRenderer(int row, int column) {
		Object value = super.getValueAt(row, column);

		if (value == null)
			value = "";

		if (tableType.equals("file") && value instanceof String) {
			if (value.equals("Delete")) {
				return deleteButton_render;
			}
		}

		else if (value instanceof DeleteButtonCellRenderer) {
			return deleteButton_render;
		}

		else if (value instanceof String && column != 0 && column != 2) {
			// String val = (String) value;
			if (value.equals("sysIncludePath"))
				return browsePathSys_render;

			else if (value.equals("userIncludePath"))
				return browsePathUser_render;
		} else if (value instanceof Integer)
			return integer_render;

		// only for option table
		else if (value instanceof String && column == 1
				&& tableType.equals("option")) {
			return text_render;
		}

		else if (value instanceof Option) {
			option_render.option = (Option) value;
			return option_render;
		}

		else if (value instanceof Boolean)
			return boolean_render;

		return super.getCellRenderer(row, column);
	}

	/**
	 * Uses the editableCols field to specify which columns can be edited and
	 * which cannot. This method is called by swing on specific cells to check
	 * if they are editable.
	 * 
	 * @param row
	 *            The row of the cell.
	 * @param col
	 *            The column of the cell.
	 * 
	 * @return A boolean representing if the cell is editable or not.
	 */
	public boolean isCellEditable(int row, int col) {
		boolean found = false;
		for (int i = 0; i < editableCols.length; i++) {
			if (col == editableCols[i]) {
				found = true;
				break;
			}
		}

		return found;
	}

	/**
	 * Sets the toolTip text that describes each option.
	 * 
	 * @param e
	 *            The mouse event.
	 * 
	 * @return The Tool Tip Text for the desired cell.
	 */
	public String getToolTipText(MouseEvent e) {
		String tip = null;
		java.awt.Point p = e.getPoint();
		int rowIndex = rowAtPoint(p);
		int colIndex = columnAtPoint(p);

		try {
			if (colIndex == 0 && tableType == "option") {
				tip = ((Option) getValueAt(rowIndex, colIndex)).description();

			}
		} catch (RuntimeException e1) {
			// catch null pointer exception if mouse is over an empty line
		}

		return tip;
	}

	/**
	 * Adds a SaveTableListener.
	 * 
	 * @param listener
	 *            The Listener we would like to add.
	 */
	public void addSaveTableListener(SaveTableListener listener) {
		listenerList.add(SaveTableListener.class, listener);
	}
	
	/**
	 * Removes a SaveTableListener.
	 * 
	 * @param listener
	 *            The Listener we would like to remove.
	 */
	public void removeSaveTableListener(SaveTableListener listener) {
		listenerList.remove(SaveTableListener.class, listener);
	}

	/**
	 * Used to fire save Table events that can trigger saves in the GUI.
	 * 
	 * @param evt
	 *            The event we will fire
	 */
	void fireSaveTableEvent(SaveTableEvent evt) {
		Object[] listeners = listenerList.getListenerList();
		for (int i = 0; i < listeners.length; i = i + 2) {
			if (listeners[i] == SaveTableListener.class) {
				((SaveTableListener) listeners[i + 1]).SaveTableTriggered(evt);
			}
		}
	}

	@Override
	public void mouseClicked(MouseEvent e) {
		java.awt.Point p = e.getPoint();
		int colIndex = columnAtPoint(p);
		try {
			if (colIndex == 1 && tableType == "option") {
				fireSaveTableEvent(new SaveTableEvent(this));
				System.out.println("fire table save");
			} else if (colIndex == 2 && tableType == "input") {
				// save input code of some kind
			}
		} catch (RuntimeException e1) {
			// catch null pointer exception if mouse is over an empty line
		}

	}

	@Override
	public void mousePressed(MouseEvent e) {
	}

	@Override
	public void mouseReleased(MouseEvent e) {
	}

	@Override
	public void mouseEntered(MouseEvent e) {
	}

	@Override
	public void mouseExited(MouseEvent e) {
	}

}