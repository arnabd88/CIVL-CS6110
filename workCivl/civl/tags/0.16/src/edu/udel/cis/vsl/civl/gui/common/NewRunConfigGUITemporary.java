package edu.udel.cis.vsl.civl.gui.common;

import java.awt.CardLayout;
import java.awt.Component;
import java.awt.Font;
import java.awt.Window;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;

import javax.swing.AbstractAction;
import javax.swing.Action;
import javax.swing.ImageIcon;
import javax.swing.JButton;
import javax.swing.JFileChooser;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTabbedPane;
import javax.swing.JTable;
import javax.swing.JTextArea;
import javax.swing.JTextField;
import javax.swing.JTree;
import javax.swing.SwingUtilities;
import javax.swing.border.EtchedBorder;
import javax.swing.border.TitledBorder;
import javax.swing.event.TreeSelectionEvent;
import javax.swing.event.TreeSelectionListener;
import javax.swing.filechooser.FileNameExtensionFilter;
import javax.swing.table.DefaultTableModel;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeModel;
import javax.swing.tree.TreePath;

import edu.udel.cis.vsl.civl.config.IF.CIVLConstants;
import edu.udel.cis.vsl.gmc.Option;

/**
 * This class is the main frame for the CIVL GUI.
 * 
 * @author Steven Noyes (noyes)
 * 
 */
// TODO: CHANGE absoluteLayouts(setLayout(null)) to groupLayouts
@SuppressWarnings({ "serial", "unused" })
public class NewRunConfigGUITemporary extends JFrame {

//	private static final long serialVersionUID = 5152675076717228871L;
//
//	/**
//	 * The views for each command represented as a card layout in this JPanel.
//	 */
//	private JPanel viewCards;
//
//	/**
//	 * The layout for the viewCards JPanel.
//	 */
//	private CardLayout viewCardsLayout;
//
//	/**
//	 * The JPanel that contains ta_header, ta_header_info and the JLabel icon.
//	 */
//	private JPanel p_header;
//
//	/**
//	 * 
//	 * The panel that contains the JTree of commands.
//	 */
//	private JPanel p_commands;
//
//	/**
//	 * A simple container for GUI organization.
//	 */
//	private JPanel p_container;
//
//	/**
//	 * The JTextArea that contains the header text.
//	 */
//	private JTextArea ta_header;
//
//	/**
//	 * The JTextArea that contains the description of the chosen command.
//	 */
//	private JTextArea ta_header_info;
//
//	/**
//	 * The CIVL logo.
//	 */
//	private JLabel lb_icon;
//
//	/**
//	 * A simple label. (Name: )
//	 */
//	private JLabel lb_name;
//
//	/**
//	 * Explains what the 'new' button does.
//	 */
//	private JLabel lb_new;
//
//	/**
//	 * Explains what the 'duplicate' button does.
//	 */
//	private JLabel lb_duplicate;
//
//	/**
//	 * Explains what the 'delete' button does.
//	 */
//	private JLabel lb_delete;
//
//	/**
//	 * The JTree that contains the list of commands.
//	 */
//	private JTree jt_commands;
//
//	/**
//	 * The root of the t_commands JTree.
//	 */
//	private DefaultMutableTreeNode top;
//
//	/**
//	 * The JTextField that displays the chosen file.
//	 */
//	private JTextField tf_chosenFile_pa;
//	private JTextField tf_chosenFile_pp;
//	private JTextField tf_chosenFile_rp;
//	private JTextField tf_chosenFile_ru;
//	private JTextField tf_chosenFile_vf;
//
//	/**
//	 * The JTextField in which the user names their run configuration.
//	 */
//	private JTextField tf_name;
//
//	/**
//	 * Reverts all options in tbl_optTable to their default values.
//	 */
//	private JButton bt_revert;
//
//	/**
//	 * Applies all option changes to the run configuration.
//	 */
//	private JButton bt_apply;
//
//	/**
//	 * Cancels the program, and closes the GUI.
//	 */
//	private JButton bt_cancel;
//
//	/**
//	 * Runs the selected configuration.
//	 */
//	private JButton bt_run;
//
//	/**
//	 * Creates a new run configuration.
//	 */
//	private JButton bt_new;
//
//	/**
//	 * Duplicates the currently selected run configuration.
//	 */
//	private JButton bt_duplicate;
//
//	/**
//	 * Deletes the currently selected run configuration.
//	 */
//	private JButton bt_deleteConfig;
//
//	/**
//	 * The JTable that displays all of the options the user can choose from.
//	 */
//	private JTable tbl_optTable_ru;
//	private JTable tbl_optTable_vf;
//
//	/**
//	 * The JTable that displays all of the inputs the user can specify values
//	 * for.
//	 */
//	private JTable tbl_inputTable_ru;
//	private JTable tbl_inputTable_vf;
//
//	/**
//	 * The list of CIVL_Commands that are available to the user.
//	 */
//	private CIVL_Command[] commands;
//
//	/**
//	 * The selected file to create a run configuration for.
//	 */
//	private File selectedFile;
//
//	/**
//	 * The currently selected option(Option).
//	 */
//	public Option selectedOp;
//
//	/**
//	 * The currently selected command(CIVL_Command).
//	 */
//	public CIVL_Command selectedCom;
//
//	/**
//	 * A list of all the options that CIVL currently supports.
//	 */
//	private Option[] options;
//
//	/**
//	 * The currently selected <code>RunConfigurationDataNode</code>.
//	 */
//	private RunConfigDataNode currConfig;
//
//	/**
//	 * A Map of all of the saved configurations that the user has created. TODO:
//	 * possibly eliminate this as it may not be terribly necessary.
//	 */
//	private HashMap<String, RunConfigDataNode> savedConfigs = new HashMap<String, RunConfigDataNode>();
//
//	/**
//	 * The number of run configurations that have been created but not named in
//	 * this session.
//	 */
//	private int newConfigsNum;
//
//	/**
//	 * The panel that explains to the user how to create new configurations etc.
//	 */
//	private JPanel p_info;
//
//	/**
//	 * The JPanel(with cards Layout) that each command has. These will contain
//	 * cards that switch the view based on what configuration is selected.
//	 * 
//	 */
//	private JPanel p_parseCards;
//	private JPanel p_preprocCards;
//	private JPanel p_replayCards;
//	private JPanel p_runCards;
//	private JPanel p_verifyCards;
//
//	private CardLayout parseCardsLayout;
//	private CardLayout preprocCardsLayout;
//	private CardLayout replayCardsLayout;
//	private CardLayout runCardsLayout;
//	private CardLayout verifyCardsLayout;
//
//	/**
//	 * The action Listener for the file browse button.
//	 */
//	private ActionListener browse;
//
//	/**
//	 * The action Listener for the revert button.
//	 */
//	private ActionListener revert;
//
//	/**
//	 * The action Listener for the 'new' button.
//	 */
//	private ActionListener newConfig;
//
//	/**
//	 * The action Listener for the apply button.
//	 */
//	private ActionListener apply;
//
//	/**
//	 * The action Listener for the cancel button.
//	 */
//	private ActionListener close;
//
//	public NewRunConfigGUITemporary() {
//		this.setSize(1200, 700);
//		this.setVisible(true);
//		this.setDefaultCloseOperation(EXIT_ON_CLOSE);
//		getContentPane().setLayout(null);
//
//		// TODO: this number should be 0 + however many configurations have the
//		// name in the form:
//		// NewRunConfiguration(i)
//		int additionalNewConfigs = 0;
//		newConfigsNum = 0 + additionalNewConfigs;
//
//		initListeners();
//		initJLabel();
//		initJTextField();
//		initJTextArea();
//		initJButton();
//		initJPanel();
//	}
//
//	/**
//	 * Function that may be used later to reduce the number of instances of
//	 * components that are created, currently does not work.
//	 */
//	public void drawView() {
//		HashMap<String, Object> optValMap = currConfig.getOptValMap();
//		ArrayList<Object> valCollection = new ArrayList<Object>();
//		for (int i = 0; i < optValMap.size(); i++) {
//			Object key = selectedCom.getAllowedOptions()[i].name();
//			Object element = optValMap.get(key);
//			valCollection.add(i, element);
//		}
//		DefaultTableModel optModel_ru = (DefaultTableModel) tbl_optTable_ru
//				.getModel();
//		for (int i = 0; i < optModel_ru.getRowCount(); i++) {
//			optModel_ru.setValueAt(valCollection.get(i), i, 1);
//		}
//		// sp_optTable_ru.setViewportView(tbl_optTable_ru);
//	}
//
//	/**
//	 * This function parses the chosen file for all inputs and places them in a
//	 * <code>LinkedList</code>.
//	 * 
//	 * @return The <code>LinkedList</code> containing all of the inputs.
//	 */
//	// TODO: fix some minor parsing issues i.e arrays etc
//	// FIX: Possible use pre-built parsers in CIVL. The issue is it creates poor
//	// code design, ask Siegel/Manchun about this.
//	public LinkedList<CIVL_Input> parseInputs() {
//		BufferedReader bReader = null;
//		LinkedList<CIVL_Input> inputs = new LinkedList<CIVL_Input>();
//		try {
//			bReader = new BufferedReader(new FileReader(selectedFile.getPath()));
//		} catch (FileNotFoundException e) {
//			e.printStackTrace();
//		}
//		String line;
//
//		try {
//			while ((line = bReader.readLine()) != null) {
//				if (line.startsWith("$input")) {
//					String[] lineSplit = line.split(" ");
//					String name = lineSplit[2].substring(0,
//							lineSplit[2].length() - 1);
//					String type = lineSplit[1];
//					inputs.add(new CIVL_Input(name, type));
//				}
//			}
//		} catch (IOException e) {
//			e.printStackTrace();
//		}
//		try {
//			bReader.close();
//		} catch (IOException e) {
//			e.printStackTrace();
//		}
//		return inputs;
//	}
//
//	/**
//	 * Populates the input table of the current view with all of the inputs
//	 * returned by <code>parseInputs()</code>.
//	 */
//	// TODO: Figure out why inputs show up for runconfigs x+2 instead of run configs x.
//	//also the file name shows up x+1 away
//	//only applies to newConfig(x)
//	public void setInputs() {
//		CIVLTable currTable = null;
//		if (selectedCom.getName() == "run") {
//			currTable = (CIVLTable) tbl_inputTable_ru;
//
//		} else if (selectedCom.getName() == "verify") {
//			currTable = (CIVLTable) tbl_inputTable_vf;
//		}
//
//		LinkedList<CIVL_Input> inputs = parseInputs();
//		final DefaultTableModel inputModel = (DefaultTableModel) currTable
//				.getModel();
//
//		int rowCount;
//		//if ((rowCount = inputModel.getRowCount()) > 0) {
//		//	for (int i = 0; i < rowCount; i++)
//		//		inputModel.removeRow(i);
//		//}
//
//		for (int i = 0; i < inputs.size(); i++) {
//			CIVL_Input currInput = inputs.get(i);
//			if (currInput.getType().equals("Boolean")
//					|| currInput.getType().equals("boolean"))
//				inputModel.addRow(new Object[] { currInput.getName(),
//						currInput.getType(), true });
//			else {
//				inputModel.addRow(new Object[] { currInput.getName(),
//						currInput.getType(), "" });
//			}
//		}
//		revalidate();
//		repaint();
//	}
//
//	/**
//	 * Gets the <code>CIVL_Command</code> associated with the input String,
//	 * which represents a command name.
//	 * 
//	 * @param comName
//	 *            The name of a command as a String
//	 * @return The <code>CIVL_Command</code> with that name.
//	 */
//	public CIVL_Command getCommand(String comName) {
//		CIVL_Command com = null;
//		for (int i = 0; i < commands.length; i++) {
//			if (commands[i].getName() == comName) {
//				com = commands[i];
//				break;
//			}
//		}
//		return com;
//	}
//
//	/**
//	 * Given an option name(String), this function gets the option associated
//	 * with it from the list.
//	 * 
//	 * @param adOpt
//	 *            The array that contains all of the options that CIVL has.
//	 * @param optText
//	 *            The text of the option to retrieve.
//	 * 
//	 * @return The option that we retrieved from adOpt.
//	 */
//	public Option getOption(String optText) {
//		for (int i = 0; i < options.length; i++) {
//			if (options[i].name() == optText) {
//				selectedOp = options[i];
//				break;
//			}
//		}
//		return selectedOp;
//	}
//
//	/**
//	 * Creates the parse view.
//	 */
//	public JTabbedPane initParse() {
//		JTabbedPane parseView = new JTabbedPane();
//		JPanel tab_chooseFile = new JPanel();
//		JTextField tf_chosenFile = new JTextField();
//		JLabel lb_chosenFile = new JLabel("Chosen File:");
//		JButton bt_browse = new JButton("Browse...");
//
//		tab_chooseFile.setLayout(null);
//		parseView.setName("parse");
//
//		tf_chosenFile.setBounds(6, 21, 805, 28);
//		lb_chosenFile.setBounds(6, 6, 100, 16);
//		bt_browse.setBounds(823, 22, 117, 29);
//
//		bt_browse.addActionListener(browse);
//
//		tab_chooseFile.add(lb_chosenFile);
//		tab_chooseFile.add(tf_chosenFile);
//		tab_chooseFile.add(bt_browse);
//
//		parseView.addTab("New tab", null, tab_chooseFile, null);
//
//		tf_chosenFile_pa = tf_chosenFile;
//
//		CIVL_Command parse = new CIVL_Command("parse",
//				"show result of preprocessing and parsing filename",
//				new Option[] {}, false, p_parseCards);
//
//		commands[0] = parse;
//
//		return parseView;
//	}
//
//	/**
//	 * Creates the preprocess view.
//	 */
//	public JTabbedPane initPreproc() {
//		JTabbedPane preprocView = new JTabbedPane();
//		JPanel tab_chooseFile = new JPanel();
//		JTextField tf_chosenFile = new JTextField();
//		JLabel lb_chosenFile = new JLabel("Chosen File:");
//		JButton bt_browse = new JButton("Browse...");
//
//		tab_chooseFile.setLayout(null);
//		preprocView.setName("preprocess");
//
//		tf_chosenFile.setBounds(6, 21, 805, 28);
//		lb_chosenFile.setBounds(6, 6, 100, 16);
//		bt_browse.setBounds(823, 22, 117, 29);
//
//		bt_browse.addActionListener(browse);
//
//		tab_chooseFile.add(lb_chosenFile);
//		tab_chooseFile.add(tf_chosenFile);
//		tab_chooseFile.add(bt_browse);
//
//		preprocView.addTab("New tab", null, tab_chooseFile, null);
//
//		tf_chosenFile_pp = tf_chosenFile;
//
//		CIVL_Command preprocess = new CIVL_Command("preprocess",
//				"show result of preprocessing filename", new Option[] {},
//				false, p_preprocCards);
//
//		commands[1] = preprocess;
//
//		return preprocView;
//	}
//
//	/**
//	 * Creates the replay view.
//	 */
//	public JTabbedPane initReplay() {
//		JTabbedPane replayView = new JTabbedPane();
//		JPanel tab_chooseFile = new JPanel();
//		JTextField tf_chosenFile = new JTextField();
//		JLabel lb_chosenFile = new JLabel("Chosen File:");
//		JButton bt_browse = new JButton("Browse...");
//
//		tab_chooseFile.setLayout(null);
//		replayView.setName("replay");
//
//		tf_chosenFile.setBounds(6, 21, 805, 28);
//		lb_chosenFile.setBounds(6, 6, 100, 16);
//		bt_browse.setBounds(823, 22, 117, 29);
//
//		bt_browse.addActionListener(browse);
//
//		tab_chooseFile.add(lb_chosenFile);
//		tab_chooseFile.add(tf_chosenFile);
//		tab_chooseFile.add(bt_browse);
//
//		replayView.addTab("New tab", null, tab_chooseFile, null);
//
//		tf_chosenFile_rp = tf_chosenFile;
//
//		CIVL_Command replay = new CIVL_Command("replay",
//				"replay trace for program filename", new Option[] {}, false,
//				p_replayCards);
//
//		commands[2] = replay;
//
//		return replayView;
//	}
//
//	/**
//	 * Creates the run view.
//	 */
//	public JTabbedPane initRun() {
//		JLabel lb_chosenFile = new JLabel("Chosen File:");
//		JTextField tf_chosenFile = new JTextField();
//		JTabbedPane runView = new JTabbedPane();
//		JPanel tab_chooseFile = new JPanel();
//		JPanel tab_setOptions_ru = new JPanel();
//		JPanel tab_setInputs_ru = new JPanel();
//		JButton bt_browse = new JButton("Browse...");
//
//		tab_setOptions_ru.setLayout(null);
//		tab_setInputs_ru.setLayout(null);
//		tab_chooseFile.setLayout(null);
//		runView.setName("run");
//
//		JScrollPane sp_optTable = new JScrollPane();
//		JScrollPane sp_inputTable = new JScrollPane();
//		sp_optTable.setBounds(6, 6, 967 - 36, 425);
//		sp_inputTable.setBounds(6, 6, 967 - 36, 425);
//		lb_chosenFile.setBounds(6, 6, 100, 16);
//		tf_chosenFile.setBounds(6, 21, 805, 28);
//		bt_browse.setBounds(823, 22, 117, 29);
//
//		bt_browse.addActionListener(browse);
//
//		final JTable tbl_optTable = new CIVLTable(new int[] { 1, 2 }, "option");
//		JTable tbl_inputTable = new CIVLTable(new int[] { 2 }, "input");
//		sp_optTable.setViewportView(tbl_optTable_ru);
//		sp_inputTable.setViewportView(tbl_inputTable_ru);
//
//		tbl_optTable.setModel(new DefaultTableModel(null, new String[] {
//				"Option", "Value", "Default" }));
//		tbl_inputTable.setModel(new DefaultTableModel(null, new String[] {
//				"Variable", "Type", "Value" }));
//
//		tbl_optTable.setCellSelectionEnabled(true);
//		tbl_inputTable.setCellSelectionEnabled(true);
//
//		tbl_optTable.setRowHeight(30);
//		tbl_inputTable.setRowHeight(30);
//
//		final DefaultTableModel optModel_ru = (DefaultTableModel) tbl_optTable
//				.getModel();
//
//		@SuppressWarnings("serial")
//		Action defaultize = new AbstractAction() {
//			public void actionPerformed(ActionEvent e) {
//				DefaultTableModel currOptModel = optModel_ru;
//				JTable currTable = tbl_optTable;
//
//				int modelRow = currTable.getSelectedRow();
//				Object valToDefault = currOptModel.getValueAt(modelRow, 1);
//				Option optToDefault = (Option) currOptModel.getValueAt(
//						modelRow, 0);
//
//				if (valToDefault instanceof Boolean) {
//					Boolean defValue = (Boolean) optToDefault.defaultValue();
//
//					// MAIN DEFAULT ACTION:
//					currTable.setValueAt(defValue, modelRow, 1);
//				}
//
//				else
//					currOptModel.setValueAt(optToDefault.defaultValue(),
//							modelRow, 1);
//				repaint();
//			}
//		};
//
//		//CIVL_Command run = new CIVL_Command("run", "run program filename",
//		//		options, true, p_runCards);
//
//		// options for RUN
//		for (int i = 0; i < run.getAllowedOptions().length; i++) {
//			optModel_ru.addRow(new Object[] { options[i],
//					options[i].defaultValue(), "Default" });
//			new ButtonColumn(tbl_optTable, defaultize, 2);
//		}
//
//		tab_chooseFile.add(lb_chosenFile);
//		tab_chooseFile.add(tf_chosenFile);
//		tab_chooseFile.add(bt_browse);
//
//		tab_setOptions_ru.add(sp_optTable);
//		tab_setInputs_ru.add(sp_inputTable);
//
//		runView.addTab("Choose File", null, tab_chooseFile, null);
//		runView.addTab("Options", null, tab_setOptions_ru, null);
//		runView.addTab("Inputs", null, tab_setInputs_ru, null);
//
//		tbl_optTable_ru = tbl_optTable;
//		tbl_inputTable_ru = tbl_inputTable;
//		// sp_optTable_ru = sp_optTable;
//		// sp_inputTable_ru = sp_inputTable;
//		tf_chosenFile_ru = tf_chosenFile;
//
//		commands[3] = run;
//
//		return runView;
//	}
//
//	/**
//	 * Creates the verify view.
//	 */
//	public JTabbedPane initVerify() {
//		JTabbedPane verifyView = new JTabbedPane();
//		JPanel tab_chooseFile = new JPanel();
//		JPanel tab_setOptions = new JPanel();
//		JPanel tab_setInputs = new JPanel();
//		JLabel lb_chosenFile = new JLabel("Chosen File:");
//		JTextField tf_chosenFile = new JTextField();
//		JButton bt_browse = new JButton("Browse...");
//
//		tab_setOptions.setLayout(null);
//		tab_setInputs.setLayout(null);
//		tab_chooseFile.setLayout(null);
//		verifyView.setName("verify");
//
//		JScrollPane sp_optTable = new JScrollPane();
//		JScrollPane sp_inputTable = new JScrollPane();
//
//		sp_optTable.setBounds(6, 6, 967 - 36, 425);
//		sp_inputTable.setBounds(6, 6, 967 - 36, 425);
//		lb_chosenFile.setBounds(6, 6, 100, 16);
//		tf_chosenFile.setBounds(6, 21, 805, 28);
//		bt_browse.setBounds(823, 22, 117, 29);
//
//		bt_browse.addActionListener(browse);
//
//		final JTable tbl_optTable = new CIVLTable(new int[] { 1, 2 }, "option");
//		JTable tbl_inputTable = new CIVLTable(new int[] { 2 }, "input");
//
//		sp_optTable.setViewportView(tbl_optTable);
//		sp_inputTable.setViewportView(tbl_inputTable);
//		tbl_optTable.setModel(new DefaultTableModel(null, new String[] {
//				"Option", "Value", "Default" }));
//
//		tbl_inputTable.setModel(new DefaultTableModel(null, new String[] {
//				"Variable", "Type", "Value" }));
//
//		tbl_optTable.setCellSelectionEnabled(true);
//		tbl_inputTable.setCellSelectionEnabled(true);
//
//		tbl_optTable.setRowHeight(30);
//		tbl_inputTable.setRowHeight(30);
//		final DefaultTableModel optModel_vf = (DefaultTableModel) tbl_optTable
//				.getModel();
//
//		@SuppressWarnings("serial")
//		Action defaultize = new AbstractAction() {
//			public void actionPerformed(ActionEvent e) {
//				DefaultTableModel currOptModel = optModel_vf;
//
//				int modelRow = tbl_optTable.getSelectedRow();
//				Object valToDefault = currOptModel.getValueAt(modelRow, 1);
//				Option optToDefault = (Option) currOptModel.getValueAt(
//						modelRow, 0);
//				if (valToDefault instanceof Boolean) {
//					Boolean defValue = (Boolean) optToDefault.defaultValue();
//
//					// MAIN DEFAULT ACTION:
//					tbl_optTable.setValueAt(defValue, modelRow, 1);
//				}
//
//				else
//					currOptModel.setValueAt(optToDefault.defaultValue(),
//							modelRow, 1);
//				repaint();
//			}
//		};
//
//		CIVL_Command verify = new CIVL_Command("verify",
//				"verify program filename", options, true, p_verifyCards);
//
//		// options for VERIFY
//		for (int i = 0; i < verify.getAllowedOptions().length; i++) {
//			optModel_vf.addRow(new Object[] { options[i],
//					options[i].defaultValue(), "Default" });
//			new ButtonColumn(tbl_optTable, defaultize, 2);
//		}
//
//		tab_chooseFile.add(lb_chosenFile);
//		tab_chooseFile.add(tf_chosenFile);
//		tab_chooseFile.add(bt_browse);
//
//		tab_setOptions.add(sp_optTable);
//		tab_setInputs.add(sp_inputTable);
//
//		tbl_optTable_vf = tbl_optTable;
//		tbl_inputTable_vf = tbl_inputTable;
//		tf_chosenFile_vf = tf_chosenFile;
//
//		verifyView.addTab("Choose File", null, tab_chooseFile, null);
//		verifyView.addTab("Options", null, tab_setOptions, null);
//		verifyView.addTab("Inputs", null, tab_setInputs, null);
//
//		commands[4] = verify;
//
//		return verifyView;
//	}
//
//	/**
//	 * Creates all of the <code>CIVL_Command</code> that the GUI will need.
//	 */
//	public void initCommands() {
//		commands = new CIVL_Command[5];
//		options = CIVLConstants.getAllOptions();
//
//		p_parseCards = new JPanel();
//		p_preprocCards = new JPanel();
//		p_replayCards = new JPanel();
//		p_runCards = new JPanel();
//		p_verifyCards = new JPanel();
//
//		parseCardsLayout = new CardLayout();
//		preprocCardsLayout = new CardLayout();
//		replayCardsLayout = new CardLayout();
//		runCardsLayout = new CardLayout();
//		verifyCardsLayout = new CardLayout();
//
//		p_parseCards.setLayout(parseCardsLayout);
//		p_preprocCards.setLayout(preprocCardsLayout);
//		p_replayCards.setLayout(replayCardsLayout);
//		p_runCards.setLayout(runCardsLayout);
//		p_verifyCards.setLayout(verifyCardsLayout);
//
//		// TODO: these calls shouldn't be here, however certain parts of these
//		// functions are need to be called to avoid code dependencies in other
//		// initialization functions, fix this bad code design
//		initParse();
//		initPreproc();
//		initReplay();
//		initRun();
//		initVerify();
//
//	}
//
//	/**
//	 * Creates the JPanel that will display all of the cards. All cards(JPanels)
//	 * are now added to the new JPanel.
//	 */
//	public void initCards() {
//		p_info = new JPanel();
//		p_info.setLayout(null);
//		viewCardsLayout = new CardLayout();
//
//		viewCards = new JPanel();
//
//		viewCards.setBorder(new TitledBorder(null, null, TitledBorder.LEADING,
//				TitledBorder.TOP, null, null));
//		viewCards.setBounds(0, 34, 967, 488);
//		viewCards.setLayout(viewCardsLayout);
//
//		viewCards.add(commands[0].getView(), "parse");
//		viewCards.add(commands[1].getView(), "preprocess");
//		viewCards.add(commands[2].getView(), "replay");
//		viewCards.add(commands[3].getView(), "run");
//		viewCards.add(commands[4].getView(), "verify");
//		viewCards.add(p_info, "info");
//
//	}
//
//	/**
//	 * Creates and sets up all of the JPanels in the GUI.
//	 */
//	public void initJPanel() {
//		p_commands = new JPanel();
//		p_header = new JPanel();
//		p_container = new JPanel();
//		p_container
//				.setBorder(new EtchedBorder(EtchedBorder.LOWERED, null, null));
//		p_commands.setBorder(new TitledBorder(null, "Commands",
//				TitledBorder.LEADING, TitledBorder.TOP, null, null));
//
//		p_commands.setLayout(null);
//		p_container.setLayout(null);
//		p_header.setLayout(null);
//
//		p_container.setBounds(227, 65, 967, 566);
//		p_commands.setBounds(10, 99, 205, 573);
//		p_header.setBounds(0, 0, 1200, 53);
//
//		initCommands();
//		initJTable();
//		initCards();
//		initJTree();
//
//		getContentPane().add(p_container);
//		getContentPane().add(p_header);
//		getContentPane().add(p_commands);
//
//		getContentPane().add(bt_cancel);
//		getContentPane().add(bt_run);
//		getContentPane().add(bt_new);
//		getContentPane().add(bt_duplicate);
//		getContentPane().add(bt_deleteConfig);
//		p_header.add(lb_icon);
//		p_commands.add(jt_commands);
//		p_header.add(ta_header_info);
//		p_header.add(ta_header);
//		p_container.add(viewCards);
//		p_container.add(bt_apply);
//		p_container.add(bt_revert);
//		p_container.add(tf_name);
//		p_container.add(lb_name);
//		p_info.add(lb_new);
//		p_info.add(lb_duplicate);
//		p_info.add(lb_delete);
//	}
//
//	public void initListeners() {
//		browse = new ActionListener() {
//			public void actionPerformed(ActionEvent e) {
//				String examplesPath = "/Users/noyes/Documents/workspace/CIVL/examples";
//
//				File start = new File(examplesPath);
//				final JFileChooser chooser = new JFileChooser();
//				chooser.setCurrentDirectory(start);
//				FileNameExtensionFilter filter = new FileNameExtensionFilter(
//						"CIVL Files (.cvl)", "cvl");
//				chooser.setFileFilter(filter);
//				chooser.addActionListener(new ActionListener() {
//					public void actionPerformed(ActionEvent e) {
//						selectedFile = chooser.getSelectedFile();
//						if (selectedCom.getName() == "parse") {
//							tf_chosenFile_pa.setText(selectedFile.getName());
//						} else if (selectedCom.getName() == "preprocess") {
//							tf_chosenFile_pp.setText(selectedFile.getName());
//						} else if (selectedCom.getName() == "run") {
//							tf_chosenFile_ru.setText(selectedFile.getName());
//							setInputs();
//						} else if (selectedCom.getName() == "verify") {
//							tf_chosenFile_vf.setText(selectedFile.getName());
//							setInputs();
//						}
//
//					}
//				});
//				chooser.showOpenDialog(null);
//			}
//		};
//
//		revert = new ActionListener() {
//			public void actionPerformed(ActionEvent e) {
//				JTable currTable = null;
//				Option[] selectedOptions = selectedCom.getAllowedOptions();
//				if (selectedCom.getName() == "run") {
//					currTable = tbl_optTable_ru;
//				} else if (selectedCom.getName() == "verify") {
//					currTable = tbl_optTable_vf;
//				}
//				for (int i = 0; i < selectedOptions.length; i++) {
//					Object defValue = selectedOptions[i].defaultValue();
//					currTable.setValueAt(defValue, i, 1);
//				}
//			}
//		};
//
//		newConfig = new ActionListener() {
//			public void actionPerformed(ActionEvent e) {
//				Object config = savedConfigs.get(tf_name.getText());
//				boolean dontCreate = false;
//
//				if (config != null) {
//					dontCreate = true;
//				}
//
//				if (!dontCreate) {
//					TreePath selected = jt_commands.getSelectionPath();
//
//					DefaultMutableTreeNode selectedNode = (DefaultMutableTreeNode) jt_commands
//							.getLastSelectedPathComponent();
//
//					DefaultMutableTreeNode newChild = new RunConfigDataNode(
//							selectedCom);
//					String newName = tf_name.getText();
//					if (tf_name.getText().equals(null)
//							|| tf_name.getText().equals("")) {
//						newName = "New Configuration(" + newConfigsNum + ")";
//						if (selected.getPathCount() == 2){															
//							newConfigsNum++;
//						}
//						
//					}
//					newChild.setUserObject(newName);
//					currConfig = (RunConfigDataNode) newChild;
//					currConfig.setName(newName);
//					tf_name.setText(newName);
//					
//					if (selected.getPathCount() == 2) {
//						((DefaultTreeModel) jt_commands.getModel())
//								.insertNodeInto(currConfig, selectedNode,
//										selectedNode.getChildCount());
//
//						HashMap<String, Object> optValMap = new HashMap<String, Object>();
//						Option[] opts = selectedCom.getAllowedOptions();
//
//						for (int i = 0; i < opts.length; i++) {
//							Object value = opts[i].defaultValue();
//							optValMap.put(opts[i].name(), value);
//						}
//
//						currConfig.setOptValMap(optValMap);
//						int configNum = selectedNode.getChildCount();
//						int row = 0;
//						int row_pa = 1;
//						int row_pp = 2;
//						int row_rp = 3;
//						int row_ru = 4;
//						int row_vf = 5;
//						if (selectedCom.getName().equals("run")) {
//							row = row_ru;
//							JTabbedPane newRun = initRun();
//							p_runCards.add(newRun, currConfig.getName());
//							savedConfigs.put(currConfig.getName(), currConfig);
//						} else if (selectedCom.getName().equals("verify")) {
//							row = row_vf;
//							JTabbedPane newVerify = initVerify();
//							p_verifyCards.add(newVerify, currConfig.getName());
//							savedConfigs.put(currConfig.getName(), currConfig);
//						} else if (selectedCom.getName().equals("parse")) {
//							row = row_pa;
//							JTabbedPane newParse = initParse();
//							p_parseCards.add(newParse, currConfig.getName());
//							savedConfigs.put(currConfig.getName(), currConfig);
//						} else if (selectedCom.getName().equals("preprocess")) {
//							row = row_pp;
//							JTabbedPane newPreproc = initPreproc();
//							p_preprocCards
//									.add(newPreproc, currConfig.getName());
//							savedConfigs.put(currConfig.getName(), currConfig);
//						} else if (selectedCom.getName().equals("replay")) {
//							row = row_rp;
//							JTabbedPane newReplay = initReplay();
//							p_replayCards.add(newReplay, currConfig.getName());
//							savedConfigs.put(currConfig.getName(), currConfig);
//						}
//
//						jt_commands.expandPath(selected);
//						jt_commands.setSelectionRow(row + configNum);
//
//					}
//					//tf_name.setText("");
//					
//
//				}
//				dontCreate = false;
//				
//			}
//		};
//
//		apply = new ActionListener() {
//			public void actionPerformed(ActionEvent e) {
//				JTable currTable = null;
//				if (selectedCom.getName() == "run") {
//					currTable = tbl_optTable_ru;
//				} else if (selectedCom.getName() == "verify") {
//					currTable = tbl_optTable_vf;
//				}
//				savedConfigs.remove(currConfig.getName());
//				currConfig.setName(tf_name.getText());
//				HashMap<String, Object> optValMap = new HashMap<String, Object>();
//				Option[] opts = selectedCom.getAllowedOptions();
//				for (int i = 0; i < optValMap.size(); i++) {
//					Object value = currTable.getValueAt(i, 1);
//					optValMap.put(opts[i].name(), value);
//				}
//				currConfig.setOptValMap(optValMap);
//				currConfig.setSelectedFile(selectedFile);
//				currConfig.setToSave(true);
//				savedConfigs.put(currConfig.getName(), currConfig);
//			}
//		};
//
//		close = new ActionListener() {
//			public void actionPerformed(ActionEvent e) {
//				Window window = SwingUtilities.windowForComponent((Component) e
//						.getSource());
//				window.dispose();
//			}
//		};
//
//	}
//
//	/**
//	 * Creates all of the JButtons in the GUI.
//	 */
//	public void initJButton() {
//		bt_cancel = new JButton("Cancel");
//		bt_run = new JButton("Run");
//
//		bt_revert = new JButton("Revert");
//		bt_apply = new JButton("Apply");
//		bt_new = new JButton("New");
//		bt_duplicate = new JButton("Duplicate");
//		bt_deleteConfig = new JButton("X");
//
//		bt_apply.setBounds(717, 531, 117, 29);
//		bt_revert.setBounds(844, 531, 117, 29);
//
//		bt_cancel.setBounds(1077, 643, 117, 29);
//		bt_run.setBounds(948, 643, 117, 29);
//		bt_new.setBounds(10, 65, 53, 29);
//		bt_duplicate.setBounds(59, 65, 89, 29);
//		bt_deleteConfig.setBounds(142, 65, 61, 29);
//
//		bt_cancel.addActionListener(close);
//		bt_revert.addActionListener(revert);
//		bt_apply.addActionListener(apply);
//		bt_new.addActionListener(newConfig);
//
//	}
//
//	// TODO: FILL TABLE WITH "ALLOWED" OPTIONS INSTEAD OF ALL OF THEM
//	// to do this, set the allowed options correctly when the command is created
//	// in initCommands
//	// and this will automatically be fixed. Right now each command has a list
//	// of all options for allowedOptions.
//	// Also, not all commands even need options, account for that too.
//	// TODO: POSSIBLY MAKE COLUMNS SMALLER
//	// TODO: Finish the formattedTextFields so that it only accepts
//	// numbers/Strings when necessary.
//	/**
//	 * Creates the JTables and all necessary components related to them.
//	 */
//	public void initJTable() {
//
//	}
//
//	/**
//	 * Creates all of the JLabels in the GUI, most notably the CIVL icon.
//	 */
//	public void initJLabel() {
//		lb_icon = new JLabel("");
//		lb_name = new JLabel("Name:");
//		lb_new = new JLabel(
//				"New - Press the new button to create a new run configuration of the selected type.");
//		lb_duplicate = new JLabel(
//				"Duplicate - Press the 'duplicate' button to duplicate the currently selected run configuration.");
//		lb_delete = new JLabel(
//				"Delete - Press the 'delete' button to delete the currently selected run configuration.");
//		lb_new.setBounds(6, 6, 554, 16);
//		lb_duplicate.setBounds(6, 39, 589, 16);
//		lb_delete.setBounds(6, 72, 589, 16);
//		lb_name.setBounds(9, 8, 61, 16);
//		lb_icon.setBounds(1040, 3, 207, 47);
//		lb_icon.setIcon(new ImageIcon("Images/logo.png"));
//
//	}
//
//	/**
//	 * Creates all of the text areas in the GUI.
//	 */
//	public void initJTextArea() {
//		ta_header = new JTextArea();
//		ta_header_info = new JTextArea();
//
//		ta_header.setBounds(0, 0, 1200, 22);
//		ta_header.setFont(new Font("Lucida Grande", Font.BOLD, 13));
//		ta_header.setFocusable(false);
//		ta_header.setDragEnabled(false);
//		ta_header.setText("  Create, manage and run configurations\n");
//
//		ta_header_info.setBounds(0, 21, 1200, 32);
//		ta_header_info.setText("     ");
//		ta_header_info.setFocusable(false);
//		ta_header_info.setDragEnabled(false);
//	}
//
//	/**
//	 * Creates all of the JTextFields in the GUI.
//	 */
//	public void initJTextField() {
//		tf_chosenFile_pa = new JTextField();
//		tf_chosenFile_pp = new JTextField();
//		tf_chosenFile_rp = new JTextField();
//		tf_name = new JTextField();
//
//		tf_chosenFile_pa.setBounds(6, 21, 805, 28);
//		tf_chosenFile_pp.setBounds(6, 21, 805, 28);
//		tf_chosenFile_rp.setBounds(6, 21, 805, 28);
//		tf_name.setBounds(52, 4, 905, 28);
//
//	}
//
//	/**
//	 * Creates all of the DefaultMutableTreeNodes that will be included in the
//	 * <code>t_commands</code> JTree.
//	 */
//	public void initNodes() {
//		DefaultMutableTreeNode parseNode;
//		DefaultMutableTreeNode preprocessNode;
//		DefaultMutableTreeNode replayNode;
//		DefaultMutableTreeNode runNode;
//		DefaultMutableTreeNode verifyNode;
//
//		top = new DefaultMutableTreeNode("commands");
//		parseNode = new DefaultMutableTreeNode("parse");
//		preprocessNode = new DefaultMutableTreeNode("preprocess");
//		replayNode = new DefaultMutableTreeNode("replay");
//		runNode = new DefaultMutableTreeNode("run");
//		verifyNode = new DefaultMutableTreeNode("verify");
//
//		/*
//		 * for (int i = 0; i < savedConfigs.size(); i++) { RunConfigDataNode
//		 * currConfig = savedConfigs.get(i); String currCommandName =
//		 * currConfig.getCommand().getName(); if (currCommandName == "parse")
//		 * parseNode.add(new DefaultMutableTreeNode(currConfig.getName())); else
//		 * if (currCommandName == "preprocess") preprocessNode.add(new
//		 * DefaultMutableTreeNode(currConfig .getName())); else if
//		 * (currCommandName == "replay") replayNode .add(new
//		 * DefaultMutableTreeNode(currConfig.getName())); else if
//		 * (currCommandName == "run") runNode.add(new
//		 * DefaultMutableTreeNode(currConfig.getName())); else if
//		 * (currCommandName == "verify") verifyNode .add(new
//		 * DefaultMutableTreeNode(currConfig.getName())); }
//		 */
//
//		top.add(parseNode);
//		top.add(preprocessNode);
//		top.add(replayNode);
//		top.add(runNode);
//		top.add(verifyNode);
//	}
//
//	/**
//	 * Creates the JTree that holds all of the <code>CIVL_Command</code>.
//	 */
//	//TODO: If a runconfignode is selected and the parent node is closed, a null ptr exp is thrown.
//	public void initJTree() {
//		initNodes();
//		jt_commands = new JTree(top);
//		jt_commands.setBounds(6, 22, 193, 579);
//		jt_commands.addTreeSelectionListener(new TreeSelectionListener() {
//			public void valueChanged(TreeSelectionEvent e) {
//				TreePath selected = jt_commands.getSelectionPath();
//				DefaultMutableTreeNode node = (DefaultMutableTreeNode) jt_commands
//						.getLastSelectedPathComponent();
//				String nodeString = node.toString();
//
//				if (selected.getPathCount() == 2) {
//					selectedCom = getCommand(nodeString);
//					ta_header_info.setText("     " + selectedCom.getName()
//							+ ": " + selectedCom.getDescription());
//					viewCardsLayout.show(viewCards, "info");
//					tf_name.setText("");
//				}
//
//				else if (selected.getPathCount() == 3) {
//					currConfig = (RunConfigDataNode) node;
//					viewCardsLayout.show(viewCards, selectedCom.getName());
//					DefaultMutableTreeNode child = (DefaultMutableTreeNode) jt_commands
//							.getLastSelectedPathComponent();
//					selectedCom = getCommand(child.getParent().toString());
//					System.out.println(currConfig.getName());
//					if (selectedCom.getName().equals("run"))
//						runCardsLayout.show(p_runCards, currConfig.getName());
//					else if (selectedCom.getName().equals("verify"))
//						verifyCardsLayout.show(p_verifyCards,
//								currConfig.getName());
//					else if (selectedCom.getName().equals("parse"))
//						parseCardsLayout.show(p_parseCards,
//								currConfig.getName());
//					else if (selectedCom.getName().equals("preprocess"))
//						preprocCardsLayout.show(p_preprocCards,
//								currConfig.getName());
//					else if (selectedCom.getName().equals("replay"))
//						replayCardsLayout.show(p_replayCards,
//								currConfig.getName());
//
//					tf_name.setText(currConfig.getName());
//				} else
//					ta_header_info.setText("     " + "Select a command");
//
//				revalidate();
//				repaint();
//			}
//
//		});
//		revalidate();
//		repaint();
//	}
}
