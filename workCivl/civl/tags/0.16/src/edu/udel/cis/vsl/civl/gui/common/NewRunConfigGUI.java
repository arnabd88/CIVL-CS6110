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
//
///**
// * This class is the main frame for the CIVL GUI.
// * 
// * @author Steven Noyes (noyes)
// * 
// */
@SuppressWarnings({ "unused", "serial" })
public class NewRunConfigGUI extends JFrame {
//
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
//	 * The label: "Chosen File". It indicates the JTextField that displays the
//	 * chosen file.
//	 */
//	private JLabel lb_chosenFile_pa;
//	private JLabel lb_chosenFile_pp;
//	private JLabel lb_chosenFile_rp;
//	private JLabel lb_chosenFile_ru;
//	private JLabel lb_chosenFile_vf;
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
//	 * Allows the user to browse for a file.
//	 */
//	private JButton bt_browse_pa;
//	private JButton bt_browse_pp;
//	private JButton bt_browse_rp;
//	private JButton bt_browse_ru;
//	private JButton bt_browse_vf;
//
//	/**
//	 * The JTable that displays all of the options the user can choose from.
//	 */
//	private JTable tbl_optTable_ru;
//	private JTable tbl_optTable_vf;
//
//	/**
//	 * The JScrollPane that the tbl_optTable is displayed within.
//	 */
//	private JScrollPane sp_optTable_ru;
//	private JScrollPane sp_optTable_vf;
//
//	/**
//	 * The JTable that displays all of the inputs the user can specify values
//	 * for.
//	 */
//	private JTable tbl_inputTable_ru;
//	private JTable tbl_inputTable_vf;
//
//	/**
//	 * The JScrollPane that the tbl_inputTable is displayed within.
//	 */
//	private JScrollPane sp_inputTable_ru;
//	private JScrollPane sp_inputTable_vf;
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
//	 * The tab(JPanel) that the user can Fs options from(RUN & VERIFY).
//	 */
//	//private JPanel tab_setOptions_ru;
//	private JPanel tab_setOptions_vf;
//
//	/**
//	 * The tab(JPanel) that the user can set inputs from(RUN & VERIFY).
//	 */
//	//private JPanel tab_setInputs_ru;
//	private JPanel tab_setInputs_vf;
//
//	private RunConfigDataNode currConfig;
//
//	/**
//	 * A Map of all of the saved configurations that the user has
//	 * created. TODO: possibly eliminate this as it may not be
//	 * necessary.
//	 */
//	private HashMap<String,RunConfigDataNode> savedConfigs = new HashMap<String,RunConfigDataNode>();
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
//	private JPanel p_parseCards;
//	private JPanel p_preprocCards;
//	private JPanel p_replayCards;
//	private JPanel p_runCards;
//	private JPanel p_verifyCards;
//	
//	private CardLayout runCardsLayout;
//
//	public NewRunConfigGUI() {
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
//		initJLabel();
//		initJTextField();
//		initJTextArea();
//		initJButton();
//		initJPanel();
//	}
//
//	/**
//	 * Takes an xml file and parses it to create a runConfiguration object that
//	 * will be stored in the t_commands JTree.
//	 */
//	public void runConfigFromXML() {
//
//	}
//	
//	public void drawView(){
//		HashMap<String,Object> optValMap = currConfig.getOptValMap();
//		ArrayList<Object> valCollection = new ArrayList<Object>();
//		for(int i = 0; i<optValMap.size(); i++){
//			Object key = selectedCom.getAllowedOptions()[i].name();
//			Object element = optValMap.get(key);
//			valCollection.add(i, element);
//		}
//		DefaultTableModel optModel_ru = (DefaultTableModel) tbl_optTable_ru.getModel();
//		for(int i = 0; i < optModel_ru.getRowCount(); i++){
//			optModel_ru.setValueAt(valCollection.get(i), i, 1);
//		}		
//		sp_optTable_ru.setViewportView(tbl_optTable_ru);
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
//	public void setInputs() {
//		CIVLTable currTable = null;
//		if (selectedCom.getName() == "run") {
//			currTable = (CIVLTable) tbl_optTable_ru;
//
//		} else if (selectedCom.getName() == "verify") {
//			currTable = (CIVLTable) tbl_optTable_vf;
//		}
//		
//		//CardLayout cardLayout = (CardLayout) selectedCom.getView().getLayout();
//		//JPanel currView = selectedCom.getView();
//		//currConfig.getName()
//		//int x = sp_inputTable_ru.getX();
//		//int y = sp_inputTable_ru.getY();
//		//CIVLTable inputTable = (CIVLTable) ((JScrollPane) currView
//		//		.getComponentAt(x, y)).getViewport().getView();
//		
//		LinkedList<CIVL_Input> inputs = parseInputs();
//		final DefaultTableModel inputModel = (DefaultTableModel) currTable
//				.getModel();
//
//		int rowCount;
//		if ((rowCount = inputModel.getRowCount()) > 0) {
//			for (int i = 0; i < rowCount; i++)
//				inputModel.removeRow(i);
//		}
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
//		tab_chooseFile.setLayout(null);
//		parseView.setName("parse");
//
//		tab_chooseFile.add(lb_chosenFile_pa);
//		tab_chooseFile.add(tf_chosenFile_pa);
//		tab_chooseFile.add(bt_browse_pa);
//
//		parseView.addTab("New tab", null, tab_chooseFile, null);
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
//		tab_chooseFile.setLayout(null);
//		preprocView.setName("preprocess");
//
//		tab_chooseFile.add(lb_chosenFile_pp);
//		tab_chooseFile.add(tf_chosenFile_pp);
//		tab_chooseFile.add(bt_browse_pp);
//
//		preprocView.addTab("New tab", null, tab_chooseFile, null);
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
//		tab_chooseFile.setLayout(null);
//		replayView.setName("replay");
//
//		tab_chooseFile.add(lb_chosenFile_rp);
//		tab_chooseFile.add(tf_chosenFile_rp);
//		tab_chooseFile.add(bt_browse_rp);
//
//		replayView.addTab("New tab", null, tab_chooseFile, null);
//
//		return replayView;
//	}
//
//	/**
//	 * Creates the run view.
//	 */
//	public JTabbedPane initRun() {
//		JTabbedPane runView = new JTabbedPane();
//		JPanel tab_chooseFile = new JPanel();
//		JPanel tab_setOptions_ru = new JPanel();
//		JPanel tab_setInputs_ru = new JPanel();
//		tab_setOptions_ru.setLayout(null);
//		tab_setInputs_ru.setLayout(null);
//		tab_chooseFile.setLayout(null);
//		runView.setName("run");
//		
//		tab_chooseFile.add(lb_chosenFile_ru);
//		tab_chooseFile.add(tf_chosenFile_ru);
//		tab_chooseFile.add(bt_browse_ru);
//
//		runView.addTab("Choose File", null, tab_chooseFile, null);
//		runView.addTab("Options", null, tab_setOptions_ru, null);
//		runView.addTab("Inputs", null, tab_setInputs_ru, null);
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
//		tab_setOptions_vf = new JPanel();
//		tab_setInputs_vf = new JPanel();
//		tab_setOptions_vf.setLayout(null);
//		tab_setInputs_vf.setLayout(null);
//		tab_chooseFile.setLayout(null);
//		verifyView.setName("verify");
//
//		tab_chooseFile.add(lb_chosenFile_vf);
//		tab_chooseFile.add(tf_chosenFile_vf);
//		tab_chooseFile.add(bt_browse_vf);
//
//		verifyView.addTab("Choose File", null, tab_chooseFile, null);
//		verifyView.addTab("Options", null, tab_setOptions_vf, null);
//		verifyView.addTab("Inputs", null, tab_setInputs_vf, null);
//
//		return verifyView;
//	}
//
//	/**
//	 * Creates all of the commandViews. TODO: get rid of the help view(not
//	 * needed)
//	 */
//	public void initCommandViews() {
//		initParse();
//		initPreproc();
//		initReplay();
//		initRun();
//		initVerify();
//	}
//
//	/**
//	 * Creates all of the <code>CIVL_Command</code> that the GUI will need.
//	 */
//	@SuppressWarnings("unused")
//	public void initCommands() {
//		commands = new CIVL_Command[6];
//		options = CIVLConstants.getAllOptions();		
//		
//		p_parseCards = new JPanel();
//		p_preprocCards = new JPanel();
//		p_replayCards = new JPanel();
//		p_runCards = new JPanel();
//		p_verifyCards = new JPanel();
//		
//		runCardsLayout = new CardLayout();
//		
//		p_parseCards.setLayout(new CardLayout());
//		p_preprocCards.setLayout(new CardLayout());
//		p_replayCards.setLayout(new CardLayout());
//		p_runCards.setLayout(runCardsLayout);
//		p_verifyCards.setLayout(new CardLayout());
//		
//		JTabbedPane parseView = initParse();
//		JTabbedPane preprocView = initPreproc();
//		JTabbedPane replayView = initReplay();
//		JTabbedPane runView = initRun();
//		JTabbedPane verifyView = initVerify();
//		
//		//p_runCards.add(runView);
//		
//		
//		CIVL_Command parse = new CIVL_Command("parse",
//				"show result of preprocessing and parsing filename",
//				new Option[] {}, false, p_parseCards);
//		CIVL_Command preprocess = new CIVL_Command("preprocess",
//				"show result of preprocessing filename", new Option[] {},
//				false, p_preprocCards);
//		CIVL_Command replay = new CIVL_Command("replay",
//				"replay trace for program filename", new Option[] {}, false,
//				p_replayCards);
//		CIVL_Command run = new CIVL_Command("run", "run program filename",
//				options, true, p_runCards);
//		CIVL_Command verify = new CIVL_Command("verify",
//				"verify program filename", options, true, p_verifyCards);
//				
//		/*
//		CIVL_Command parse = new CIVL_Command("parse",
//				"show result of preprocessing and parsing filename",
//				new Option[] {}, false, parseView);
//		CIVL_Command preprocess = new CIVL_Command("preprocess",
//				"show result of preprocessing filename", new Option[] {},
//				false, preprocView);
//		CIVL_Command replay = new CIVL_Command("replay",
//				"replay trace for program filename", new Option[] {}, false,
//				replayView);
//		CIVL_Command run = new CIVL_Command("run", "run program filename",
//				options, true, runView);
//		CIVL_Command verify = new CIVL_Command("verify",
//				"verify program filename", options, true, verifyView);
//				*/
//
//		commands[0] = parse;
//		commands[1] = preprocess;
//		commands[2] = replay;
//		commands[3] = run;
//		commands[4] = verify;
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
//		
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
//	/**
//	 * Creates all of the JButtons in the GUI.
//	 */
//	public void initJButton() {
//		bt_cancel = new JButton("Cancel");
//		bt_run = new JButton("Run");
//		bt_browse_pa = new JButton("Browse...");
//		bt_browse_pp = new JButton("Browse...");
//		bt_browse_rp = new JButton("Browse...");
//		bt_browse_ru = new JButton("Browse...");
//		bt_browse_vf = new JButton("Browse...");
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
//		bt_browse_pa.setBounds(823, 22, 117, 29);
//		bt_browse_pp.setBounds(823, 22, 117, 29);
//		bt_browse_rp.setBounds(823, 22, 117, 29);
//		bt_browse_ru.setBounds(823, 22, 117, 29);
//		bt_browse_vf.setBounds(823, 22, 117, 29);
//		bt_new.setBounds(10, 65, 53, 29);
//		bt_duplicate.setBounds(59, 65, 89, 29);
//		bt_deleteConfig.setBounds(142, 65, 61, 29);
//
//		ActionListener browse = new ActionListener() {
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
//					}
//				});
//				chooser.showOpenDialog(null);
//			}
//		};
//
//		bt_cancel.addActionListener(new ActionListener() {
//			public void actionPerformed(ActionEvent e) {
//				Window window = SwingUtilities.windowForComponent((Component) e
//						.getSource());
//				window.dispose();
//			}
//		});
//
//		bt_revert.addActionListener(new ActionListener() {
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
//		});
//
//		bt_apply.addActionListener(new ActionListener() {
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
//		});
//		
//		bt_new.addActionListener(new ActionListener() {
//			public void actionPerformed(ActionEvent e) {				
//				TreePath selected = jt_commands.getSelectionPath();
//				
//				DefaultMutableTreeNode selectedNode = (DefaultMutableTreeNode) jt_commands
//						.getLastSelectedPathComponent();
//				
//				
//				// DefaultMutableTreeNode newChild = new DefaultMutableTreeNode(
//				// "New Configuration(" + newConfigsNum + ")");
//				DefaultMutableTreeNode newChild = new RunConfigDataNode(
//						selectedCom);
//				String newName = tf_name.getText();
//				if (tf_name.getText().equals(null)
//						|| tf_name.getText().equals(""))
//					newName = "New Configuration(" + newConfigsNum + ")";
//				newChild.setUserObject(newName);
//				currConfig = (RunConfigDataNode) newChild;
//				currConfig.setName(newName);
//				if (selected.getPathCount() == 2){										
//					((DefaultTreeModel) jt_commands.getModel()).insertNodeInto(
//							currConfig, selectedNode,
//							selectedNode.getChildCount());
//					//selectedCom.getView().add(initRun());
//					JTabbedPane newRun = initRun();
//					//JPanel newRunOptTab = (JPanel) newRun.getComponent(1);
//					//JPanel newRunInputTab = (JPanel) newRun.getComponent(2);
//					
//					HashMap<String, Object> optValMap = new HashMap<String, Object>();
//					Option[] opts = selectedCom.getAllowedOptions();
//					
//					for (int i = 0; i < opts.length; i++) {
//						Object value = opts[i].defaultValue();
//						//System.out.println("val " + i + " " + value);
//						optValMap.put(opts[i].name(), value);
//					}
//					
//					currConfig.setOptValMap(optValMap);
//					
//					//newRunOptTab.add(sp_optTable_ru);
//					//newRunInputTab.add(sp_inputTable_ru);
//					p_runCards.add(newRun,currConfig.getName());
//					
//					//viewCards.add(selectedCom.getView(),currConfig.getName());
//					savedConfigs.put(currConfig.getName(),currConfig);
//				}
//				p_commands.repaint();
//			}
//		});
//
//		bt_browse_pa.addActionListener(browse);
//		bt_browse_pp.addActionListener(browse);
//		bt_browse_rp.addActionListener(browse);
//		bt_browse_ru.addActionListener(browse);
//		bt_browse_vf.addActionListener(browse);
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
//		sp_optTable_ru = new JScrollPane();
//		sp_optTable_vf = new JScrollPane();
//		sp_inputTable_ru = new JScrollPane();
//		sp_inputTable_vf = new JScrollPane();
//
//		sp_optTable_ru.setBounds(6, 6, 967 - 36, 425);
//		sp_optTable_vf.setBounds(6, 6, 967 - 36, 425);
//		sp_inputTable_ru.setBounds(6, 6, 967 - 36, 425);
//		sp_inputTable_vf.setBounds(6, 6, 967 - 36, 425);
//
//		tbl_optTable_ru = new CIVLTable(new int[] { 1, 2 }, "option");
//		tbl_optTable_vf = new CIVLTable(new int[] { 1, 2 }, "option");
//		tbl_inputTable_ru = new CIVLTable(new int[] { 2 }, "input");
//		tbl_inputTable_vf = new CIVLTable(new int[] { 2 }, "input");
//
//		sp_optTable_ru.setViewportView(tbl_optTable_ru);
//		sp_optTable_vf.setViewportView(tbl_optTable_vf);
//		sp_inputTable_ru.setViewportView(tbl_inputTable_ru);
//		sp_inputTable_vf.setViewportView(tbl_inputTable_vf);
//
//		tbl_optTable_ru.setModel(new DefaultTableModel(null, new String[] {
//				"Option", "Value", "Default" }));
//		tbl_optTable_vf.setModel(new DefaultTableModel(null, new String[] {
//				"Option", "Value", "Default" }));
//		tbl_inputTable_ru.setModel(new DefaultTableModel(null, new String[] {
//				"Variable", "Type", "Value" }));
//		tbl_inputTable_vf.setModel(new DefaultTableModel(null, new String[] {
//				"Variable", "Type", "Value" }));
//
//		tbl_optTable_ru.setCellSelectionEnabled(true);
//		tbl_optTable_vf.setCellSelectionEnabled(true);
//		tbl_inputTable_ru.setCellSelectionEnabled(true);
//		tbl_inputTable_vf.setCellSelectionEnabled(true);
//
//		tbl_optTable_ru.setRowHeight(30);
//		tbl_optTable_vf.setRowHeight(30);
//		tbl_inputTable_ru.setRowHeight(30);
//		tbl_inputTable_vf.setRowHeight(30);
//
//		final DefaultTableModel optModel_ru = (DefaultTableModel) tbl_optTable_ru
//				.getModel();
//		final DefaultTableModel optModel_vf = (DefaultTableModel) tbl_optTable_vf
//				.getModel();
//		tbl_inputTable_ru.getModel();
//
//		@SuppressWarnings("serial")
//		Action defaultize = new AbstractAction() {
//			public void actionPerformed(ActionEvent e) {
//				DefaultTableModel currOptModel = null;
//				JTable currTable = null;
//
//				if (selectedCom.getName() == "run") {
//					currOptModel = optModel_ru;
//					currTable = tbl_optTable_ru;
//
//				} else if (selectedCom.getName() == "verify") {
//					currOptModel = optModel_vf;
//					currTable = tbl_optTable_vf;
//				}
//
//				int modelRow = currTable.getSelectedRow();
//				Object valToDefault = currOptModel.getValueAt(modelRow, 1);
//				Option optToDefault = getOption((String) currOptModel
//						.getValueAt(modelRow, 0));
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
//		// options for RUN
//		for (int i = 0; i < (getCommand("run").getAllowedOptions().length); i++) {
//			optModel_ru.addRow(new Object[] { options[i].name(),
//					options[i].defaultValue(), "Default" });
//			new ButtonColumn(tbl_optTable_ru, defaultize, 2);
//		}
//
//		// options for VERIFY
//		for (int i = 0; i < (getCommand("verify").getAllowedOptions().length); i++) {
//			optModel_vf.addRow(new Object[] { options[i].name(),
//					options[i].defaultValue(), "Default" });
//			new ButtonColumn(tbl_optTable_vf, defaultize, 2);
//		}
//				
//		//tab_setOptions_ru.add(sp_optTable_ru);
//		//tab_setOptions_vf.add(sp_optTable_vf);
//		//tab_setInputs_ru.add(sp_inputTable_ru);
//		//tab_setInputs_vf.add(sp_inputTable_vf);
//
//		validate();
//		repaint();
//	}
//
//	/**
//	 * Creates all of the JLabels in the GUI, most notably the CIVL icon.
//	 */
//	public void initJLabel() {
//		lb_icon = new JLabel("");
//		lb_chosenFile_pa = new JLabel("Chosen File:");
//		lb_chosenFile_pp = new JLabel("Chosen File:");
//		lb_chosenFile_rp = new JLabel("Chosen File:");
//		lb_chosenFile_ru = new JLabel("Chosen File:");
//		lb_chosenFile_vf = new JLabel("Chosen File:");
//		lb_name = new JLabel("Name:");
//		lb_new = new JLabel("New - Press the new button to create a new run confiruagion of the selected type.");
//		lb_duplicate = new JLabel("Duplicate - Press the 'duplicate' button to duplicate the currently selected run configuration.");
//		lb_delete = new JLabel("Delete - Press the 'delete' button to delete the currently selected run configuration.");
//				
//		lb_chosenFile_pa.setBounds(6, 6, 100, 16);
//		lb_chosenFile_pp.setBounds(6, 6, 100, 16);
//		lb_chosenFile_rp.setBounds(6, 6, 100, 16);
//		lb_chosenFile_ru.setBounds(6, 6, 100, 16);
//		lb_chosenFile_vf.setBounds(6, 6, 100, 16);
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
//		tf_chosenFile_ru = new JTextField();
//		tf_chosenFile_vf = new JTextField();
//		tf_name = new JTextField();
//
//		tf_chosenFile_pa.setBounds(6, 21, 805, 28);
//		tf_chosenFile_pp.setBounds(6, 21, 805, 28);
//		tf_chosenFile_rp.setBounds(6, 21, 805, 28);
//		tf_chosenFile_ru.setBounds(6, 21, 805, 28);
//		tf_chosenFile_vf.setBounds(6, 21, 805, 28);
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
//		 * for (int i = 0; i < savedConfigs.size(); i++) { RunConfigData
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
//					viewCardsLayout.show(viewCards,"info");										
//				} 
//				
//				else if(selected.getPathCount() == 3){
//					currConfig = (RunConfigDataNode) node;
//					//drawView();
//					viewCardsLayout.show(viewCards, "run");
//					System.out.println(currConfig.getName());
//					//JTabbedPane newRun = initRun();
//					//JPanel newRunOptTab = (JPanel) newRun.getComponent(1);
//					//JPanel newRunInputTab = (JPanel) newRun.getComponent(2);
//					//newRunOptTab.add(sp_optTable_ru);
//					//newRunInputTab.add(sp_inputTable_ru);
//					//p_runCards.add(newRun);
//					runCardsLayout.show(p_runCards, currConfig.getName());
//				}
//				else
//					ta_header_info.setText("     " + "Select a command");
//				revalidate();
//				repaint();
//			}
//		});
//		revalidate();
//		repaint();
//	}
}
