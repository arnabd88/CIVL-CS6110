package edu.udel.cis.vsl.civl.gui.common;

import javax.swing.JFrame;
import javax.swing.JScrollPane;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.KeyEvent;
import java.io.File;
import java.util.LinkedList;
import java.util.List;
import javax.swing.AbstractAction;
import javax.swing.Action;
import javax.swing.DefaultListModel;
import javax.swing.JFileChooser;
import javax.swing.JList;
import javax.swing.JLabel;
import javax.swing.JTextArea;
import javax.swing.JButton;
import javax.swing.JTable;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;
import javax.swing.filechooser.FileNameExtensionFilter;
import javax.swing.table.DefaultTableModel;


import edu.udel.cis.vsl.civl.config.IF.CIVLConstants;
import edu.udel.cis.vsl.gmc.Option;

/**
 * 
 * The OptionFrame is an extension of JFrame that is used to specify the file,
 * command and any other additional options the user specifies
 * 
 * @author noyes
 * 
 */

@SuppressWarnings("serial")
public class OptionFrame extends JFrame {

	/**
	 * This local class is used to ensure that the first column of the
	 * <code>CIVLTable</code>(JTable) is not editable, as we do not want users to be able to
	 * change the option names in the table where selected options are
	 * displayed. 
	 * 
	 * @author noyes
	 * 
	 */
	private class CIVLTable extends JTable {
		public CIVLTable() {
			super();
		}

		@Override
		public boolean isCellEditable(int row, int col) {
			switch (col) {
			case 0:
			case 1:
				return false;
			case 2:
			default:
				return true;
			}
		}
	}

	/**
	 * This button chooses the file that the user specifies, it launches a file
	 * browser to accomplish this.
	 */
	private JButton btnChooseFile;

	/**
	 * This button selects the option that is currently selected on the
	 * <code>additionalOptions</code> JList
	 */
	private JButton optSelect;

	/**
	 * This button selects the option that is currently selected on the
	 * <code>commands</code> JList
	 */
	private JButton comSelect;

	/**
	 * This button deselects the chosen command so that the user may choose
	 * another one. This button will clear all data in the rest of the frame
	 * except for the chosen file field.
	 */
	private JButton comDeselect;

	/**
	 * This button will cancel the creation of a new run configuration and bring
	 * the user back to the <code>StartFrame</code> where they can proceed as
	 * usual.
	 */
	private JButton cancel;

	/**
	 * This button will either: 1. Save the run configuration 2. Take the user
	 * to the <code>InputFrame</code> if the chosen command is verify or run.
	 */
	private JButton finalize;

	/**
	 * This button will deselect the current file. Doing so will reset the rest
	 * of the OptionFrame, clearing all command and option choices.
	 */
	private JButton btnDeselectFile;

	/**
	 * This table is the table of options that is added to when the user selects
	 * an option from <code>additionalOptions</code>
	 */
	private JTable optTable;

	/**
	 * This JList contains all commands that CIVL currently supports.
	 */
	private JList<?> commands;

	/**
	 * This JList contains all options that CIVL currently supports.
	 */
	private JList<String> additionalOptions;

	/**
	 * This JTextArea displays the description of the currently selected command
	 * from the commands JList.
	 */
	private JTextArea comInfoText;

	/**
	 * This JTextArea displays the description of the currently selected command
	 * from the commands JList.
	 */
	private JTextArea optInfoText;

	/**
	 * This JTextArea displays the name of the currently selected file.
	 */
	private JTextArea selectedFileText;

	/**
	 * This JTextArea displays the name of the currently selected command.
	 */
	private JTextArea selectedComText;

	/**
	 * This is the scroll pane associated with <code>optTable</code>.
	 */
	private JScrollPane scrollPaneTable;

	/**
	 * This is the scroll pane associated with the <code>commands</code> JList.
	 */
	private JScrollPane scrollPaneCom;

	/**
	 * This is the scroll pane associated with the
	 * <code>additionalOptions</code> JList.
	 */
	private JScrollPane scrollPaneOpt;

	/**
	 * This boolean is a flag that will tell the launcher when it should change
	 * the frame to the <code>InputFrame</code>.
	 */
	public boolean gotoInputs;

	/**
	 * This boolean is a flag that will tell the launcher when it should change
	 * the frame to the <code>StartFrame</code>. Additionally this will save the
	 * run configuration.
	 */
	public boolean finalized;

	/**
	 * This boolean is a flag that will tell the launcher when it should change
	 * the frame to the <code>StartFrame</code>.
	 */
	public boolean cancelled;

	/**
	 * The currently selected option(String).
	 */
	public String selectedOption;

	/**
	 * The currently selected option(Option).
	 */
	public Option selectedOp;

	/**
	 * The currently selected command.
	 */
	private String selectedCommand;

	/**
	 * The currently selected file.
	 */
	private File selectedFile;

	/**
	 * All of the options that have been chosen and added to the option table.
	 */
	List<String> chosenOptions;

	public OptionFrame(boolean visible) {
		gotoInputs = false;
		cancelled = false;
		finalized = false;
		selectedOption = "";
		chosenOptions = new LinkedList<String>();
		getContentPane().setLayout(null);
		setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
		setVisible(visible);
		initJLists();
		initTextAreas();
		initLabels();
		initButtons();
		initTables();
		getContentPane().getComponents();
		enableComponents(false);
		setSize(1098, 711);
	}

	/**
	 * Given an option name(String), this function gets the option associated
	 * with it from the list.
	 * 
	 * @param adOpt
	 *            The array that contains all of the options that CIVL has.
	 * @param optText
	 *            The text of the option to retrieve.
	 * 
	 * @return The option that we retrieved from adOpt.
	 */
	public Option getOpt(Option[] adOpt, String optText) {
		for (int i = 0; i < adOpt.length; i++) {
			if (adOpt[i].name() == optText) {
				selectedOp = adOpt[i];
				break;
			}
		}
		return selectedOp;
	}

	/**
	 * This function enables or disables the various components in the option
	 * frame. This is used in conjunction with reset in order to bring the frame
	 * back to its initial state
	 * 
	 * @param enable
	 *            This boolean determines whether we want to disable all
	 *            options(If the user deselects a file) or just everything
	 *            except for the file(If the user deselects a command)
	 */
	private void enableComponents(boolean enable) {
		optSelect.setEnabled(enable);
		comSelect.setEnabled(enable);
		finalize.setEnabled(enable);
		commands.setEnabled(enable);
		additionalOptions.setEnabled(enable);
		optTable.setEnabled(enable);
		btnDeselectFile.setEnabled(enable);
		if (enable)
			comDeselect.setEnabled(!enable);
	}

	/**
	 * This function resets all fields in the components, such as the option
	 * table, the selected command and the chosen file. It is called when the
	 * user cancels the creation of a run configuration or simply chooses a new
	 * file or command.
	 * 
	 * @param totalReset
	 *            This boolean classifies the reset as "total" or not. A total
	 *            reset is when the user deselects the current file or cancels
	 *            the creation of a run configuration
	 */
	public void reset(boolean totalReset) {
		if (totalReset) {
			selectedFileText.setText("");
			selectedFile = null;
			btnChooseFile.setEnabled(true);
			// btnDeselectFile.setEnabled(false);
		}
		commands.clearSelection();
		additionalOptions.clearSelection();
		finalize.setText("Finalize");
		selectedComText.setText("");
		selectedCommand = "";
		// optTable = new JTable();
		optTable.setModel(new DefaultTableModel(null, new String[] { "Option",
				"Value", "Remove?" }));
		chosenOptions.clear();
	}

	// TODO: Add option values for each option as necessary

	/**
	 * This function initializes all of the JTables in the frame.
	 */
	public void initTables() {
		scrollPaneTable = new JScrollPane();
		scrollPaneTable.setBounds(50, 541, 385, 100);
		getContentPane().add(scrollPaneTable);
		optTable = new CIVLTable();
		scrollPaneTable.setViewportView(optTable);
		optTable.setModel(new DefaultTableModel(null, new String[] { "Option",
				"Value", "Remove?" }));
	}

	/**
	 * This function initializes all of the JLists and corresponding
	 * JScrollPanes in the frame.
	 */
	public void initJLists() {
		String[] com = { "Help", "Run", "Verify", "Replay", "Parse",
				"Preprocess" };

		final Option[] adOpt = CIVLConstants.getAllOptions();

		DefaultListModel<String> optionModel = new DefaultListModel<String>();

		scrollPaneCom = new JScrollPane();
		scrollPaneCom.setBounds(50, 90, 185, 125);
		getContentPane().add(scrollPaneCom);

		scrollPaneOpt = new JScrollPane();
		scrollPaneOpt.setBounds(50, 324, 185, 125);
		getContentPane().add(scrollPaneOpt);

		commands = new JList<Object>(com);

		for (int i = 0; i < adOpt.length; i++) {
			optionModel.addElement(adOpt[i].name());
		}

		additionalOptions = new JList<String>();
		additionalOptions.addListSelectionListener(new ListSelectionListener() {
			public void valueChanged(ListSelectionEvent e) {
				String currOpt = additionalOptions.getSelectedValue();
				if (!chosenOptions.contains(currOpt))
					optSelect.setEnabled(true);
				else
					optSelect.setEnabled(false);
				optInfoText.setText(getOpt(adOpt, currOpt).description());
			}
		});
		additionalOptions.setModel(optionModel);

		scrollPaneOpt.setViewportView(additionalOptions);
		scrollPaneCom.setViewportView(commands);
	}

	/**
	 * This function initializes all of the JTextAreas in the frame.
	 */
	public void initTextAreas() {

		comInfoText = new JTextArea();
		comInfoText.setEditable(false);
		comInfoText.setBounds(278, 90, 577, 118);
		getContentPane().add(comInfoText);

		optInfoText = new JTextArea();
		optInfoText.setEditable(false);
		optInfoText.setBounds(278, 326, 577, 153);
		getContentPane().add(optInfoText);

		selectedComText = new JTextArea();
		selectedComText.setEditable(false);
		selectedComText.setBounds(409, 220, 185, 16);
		getContentPane().add(selectedComText);

		selectedFileText = new JTextArea();
		selectedFileText.setEditable(false);
		selectedFileText.setBounds(141, 29, 225, 16);
		getContentPane().add(selectedFileText);

	}

	/**
	 * This function initializes all of the JLabels in the frame.
	 */
	public void initLabels() {
		JLabel lblChooseFile = new JLabel("Chosen File: ");
		lblChooseFile.setBounds(50, 29, 81, 16);
		getContentPane().add(lblChooseFile);

		JLabel lblCommandInformation = new JLabel("Description:");
		lblCommandInformation.setBounds(278, 62, 157, 16);
		getContentPane().add(lblCommandInformation);

		JLabel lblOption = new JLabel("Option:");
		lblOption.setBounds(50, 296, 61, 16);
		getContentPane().add(lblOption);

		JLabel lblCommand = new JLabel("Command:");
		lblCommand.setBounds(50, 62, 74, 16);
		getContentPane().add(lblCommand);

		JLabel lblSelectedCommand = new JLabel("Selected Command: ");
		lblSelectedCommand.setBounds(278, 220, 131, 16);
		getContentPane().add(lblSelectedCommand);

		JLabel label = new JLabel("Description:");
		label.setBounds(278, 298, 157, 16);
		getContentPane().add(label);

		JLabel lblSelectedOptions = new JLabel("Selected Options:");
		lblSelectedOptions.setBounds(50, 513, 117, 16);
		getContentPane().add(lblSelectedOptions);
	}

	/**
	 * This function initializes all of the JButtons in the frame.
	 */
	public void initButtons() {
		btnChooseFile = new JButton("Choose File");
		btnChooseFile.setBounds(379, 24, 117, 29);
		btnChooseFile.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				String examplesPath = "/Users/noyes/Documents/workspace/CIVL/examples";
				File start = new File(examplesPath);
				final JFileChooser chooser = new JFileChooser();
				chooser.setCurrentDirectory(start);
				FileNameExtensionFilter filter = new FileNameExtensionFilter(
						"CIVL Files (.cvl)", "cvl");
				chooser.setFileFilter(filter);
				chooser.addActionListener(new ActionListener() {
					public void actionPerformed(ActionEvent e) {
						selectedFile = chooser.getSelectedFile();
						selectedFileText.setText(selectedFile.getName());
					}
				});
				chooser.showOpenDialog(null);
				enableComponents(true);
				btnChooseFile.setEnabled(false);
				finalize.setEnabled(false);
			}
		});

		getContentPane().add(btnChooseFile);

		optSelect = new JButton("Select");
		optSelect.setBounds(86, 450, 117, 29);
		optSelect.addActionListener(new ActionListener() {
			@Override
			public void actionPerformed(ActionEvent e) {
				final DefaultTableModel tModel = (DefaultTableModel) optTable
						.getModel();
				Action delete = new AbstractAction() {
					public void actionPerformed(ActionEvent e) {
						int column = 0;
						JTable table = (JTable) e.getSource();
						int modelRow = Integer.valueOf(e.getActionCommand());
						String toAdd = (String) tModel.getValueAt(modelRow,
								column);
						((DefaultTableModel) table.getModel())
								.removeRow(modelRow);
						chosenOptions.remove(toAdd);
						additionalOptions.clearSelection();
						if (!chosenOptions.contains(toAdd))
							optSelect.setEnabled(true);
						else
							optSelect.setEnabled(false);
					}
				};
				selectedOption = additionalOptions.getSelectedValue()
						.toString();
				chosenOptions.add(selectedOption);
				// disableOption(selectedOption);
				additionalOptions.clearSelection();
				tModel.addRow(new Object[] { selectedOption, "", "Remove?" });

				ButtonColumn buttonColumn = new ButtonColumn(optTable, delete,
						2);
				buttonColumn.setMnemonic(KeyEvent.VK_D);
			}
		});
		getContentPane().add(optSelect);

		comSelect = new JButton("Select");
		comSelect.setBounds(86, 215, 117, 29);

		comSelect.addActionListener(new ActionListener() {
			@Override
			public void actionPerformed(ActionEvent e) {
				finalize.setEnabled(true);
				selectedCommand = (String) commands.getSelectedValue();
				selectedComText.setText(selectedCommand);
				// commands.setEnabled(false);
				comDeselect.setEnabled(true);
				comSelect.setEnabled(false);
				commands.clearSelection();
				if (selectedCommand == "Run" || selectedCommand == "Verify")
					finalize.setText("Set Inputs");
			}
		});
		getContentPane().add(comSelect);

		comDeselect = new JButton("Deselect");
		comDeselect.setBounds(606, 215, 117, 29);
		comDeselect.addActionListener(new ActionListener() {
			@Override
			public void actionPerformed(ActionEvent e) {
				reset(false);
				commands.setEnabled(true);
				comSelect.setEnabled(true);
				finalize.setText("Finalize");
				finalize.setEnabled(false);
			}
		});
		comDeselect.setEnabled(false);
		getContentPane().add(comDeselect);

		cancel = new JButton("Cancel");
		cancel.setBounds(966, 654, 117, 29);
		cancel.addActionListener(new ActionListener() {
			@Override
			public void actionPerformed(ActionEvent e) {
				enableComponents(false);
				reset(true);
				cancelled = true;
			}
		});
		getContentPane().add(cancel);

		finalize = new JButton("Finalize");
		finalize.setBounds(852, 654, 117, 29);
		finalize.addActionListener(new ActionListener() {

			@Override
			public void actionPerformed(ActionEvent e) {
				if (finalize.getText() != "Finalize")
					gotoInputs = true;
				else
					finalized = true;
			}
		});
		finalize.setEnabled(false);
		getContentPane().add(finalize);

		btnDeselectFile = new JButton("Deselect");
		btnDeselectFile.setBounds(508, 24, 117, 29);
		btnDeselectFile.setEnabled(false);
		btnDeselectFile.addActionListener(new ActionListener() {

			@Override
			public void actionPerformed(ActionEvent e) {
				enableComponents(false);
				reset(true);
				comDeselect.setEnabled(false);
				btnChooseFile.setEnabled(true);
			}
		});
		getContentPane().add(btnDeselectFile);
	}

	public static void main(String[] args) {
	}
}
