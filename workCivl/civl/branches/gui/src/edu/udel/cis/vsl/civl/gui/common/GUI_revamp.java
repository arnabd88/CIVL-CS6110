package edu.udel.cis.vsl.civl.gui.common;

import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Component;
import java.awt.Container;
import java.awt.FlowLayout;
import java.awt.Font;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.FocusEvent;
import java.awt.event.FocusListener;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import javax.swing.AbstractAction;
import javax.swing.Action;
import javax.swing.BorderFactory;
import javax.swing.GroupLayout;
import javax.swing.GroupLayout.Alignment;
import javax.swing.ImageIcon;
import javax.swing.JButton;
import javax.swing.JFileChooser;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTabbedPane;
import javax.swing.JTable;
import javax.swing.JTextArea;
import javax.swing.JTextField;
import javax.swing.JTree;
import javax.swing.LayoutStyle.ComponentPlacement;
import javax.swing.border.Border;
import javax.swing.border.EtchedBorder;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;
import javax.swing.event.TableModelEvent;
import javax.swing.event.TableModelListener;
import javax.swing.event.TreeSelectionEvent;
import javax.swing.event.TreeSelectionListener;
import javax.swing.filechooser.FileNameExtensionFilter;
import javax.swing.table.DefaultTableModel;
import javax.swing.table.TableColumnModel;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeModel;
import javax.swing.tree.TreePath;

import edu.udel.cis.vsl.abc.ast.node.IF.declaration.InitializerNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ConstantNode;
import edu.udel.cis.vsl.abc.err.IF.ABCException;
import edu.udel.cis.vsl.civl.config.IF.CIVLConstants;
import edu.udel.cis.vsl.civl.gui.IF.TraceViewer;
import edu.udel.cis.vsl.civl.run.IF.CommandLine.CommandLineKind;
import edu.udel.cis.vsl.civl.run.IF.CommandLine.CommandName;
import edu.udel.cis.vsl.civl.run.IF.SvcompException;
import edu.udel.cis.vsl.civl.run.IF.UserInterface;
import edu.udel.cis.vsl.civl.run.common.CIVLCommand;
import edu.udel.cis.vsl.civl.run.common.CompareCommandLine;
import edu.udel.cis.vsl.civl.run.common.NormalCommandLine;
import edu.udel.cis.vsl.civl.run.common.NormalCommandLine.NormalCommandKind;
import edu.udel.cis.vsl.gmc.CommandLineException;
import edu.udel.cis.vsl.gmc.GMCConfiguration;
import edu.udel.cis.vsl.gmc.GMCSection;
import edu.udel.cis.vsl.gmc.MisguidedExecutionException;
import edu.udel.cis.vsl.gmc.Option;
import edu.udel.cis.vsl.gmc.Option.OptionType;

/**
 * The GUI that is responsible for creating and running CIVL run configurations.
 * 
 * @author noyes
 * 
 */
public class GUI_revamp extends JFrame {

	private static final long serialVersionUID = 5152675076717228871L;

	/**
	 * A Map of all of the saved {@link RunConfigDataNode} that the user has
	 * created. The string represents the name of the configuration.
	 */
	private Map<String, RunConfigDataNode> savedConfigs = new HashMap<>();

	/**
	 * A map of all {@link Component} in the GUI.
	 */
	private Map<String, Component> componentMap;

	/**
	 * The currently selected {@link RunConfigDataNode}.
	 */
	private RunConfigDataNode currConfig;

	/**
	 * The currently enabled {@link CIVL_Command}.
	 */
	private CommandName currCommand;

	/**
	 * See the method {@link #addToMap(Component)}.
	 */
	public int i;

	/**
	 * The list of all {@link CIVLCommand}.
	 */
	private CIVL_Command[] commands;

	/**
	 * The action that defines how options are default back to their default
	 * values.
	 */
	private Action defaultize;

	/**
	 * The number of un-named {@link RunConfigDataNode}.
	 */
	private int newConfigsNum;

	/**
	 * The path to the serialized Run Configurations.
	 */
	private static String serializePath;

	/**
	 * The command line object that the GUI will use
	 */
	
	@SuppressWarnings("unused")
	private NormalCommandLine commandLine;

	/*
	 * The console string
	 */
	private String consoleString;
	private Map<String, String> consoleStats;
	private List<String> consoleStatsList;
	
	private String tempString = "";
	private String examplesPath = "";
	private CommandName lastRunCommand = null;
	private Map<String, String> tempStats = new HashMap<String, String>();
	public GUI_revamp() {
		setVisible(true);
		setDefaultCloseOperation(EXIT_ON_CLOSE);
		setSize(850, 700);
		componentMap = new HashMap<String, Component>();
		newConfigsNum = 0;

		String homeDir = System.getProperty("user.home");
		setSerializePath(homeDir + "/.CIVL");
		File f = new File(homeDir + "/.CIVL");
		f.mkdirs();

		loadSavedConfigsMap();
		initCommandsPanel();
		initContainer();
		initHeader();
		initExecute();
		createComponentMap(this);
		initLayouts();
		initListeners(this);
	}

	/**
	 * Gets the current RunConfigDataNode
	 * 
	 * @return The current RunConfigDataNode
	 */
	public RunConfigDataNode getCurrConfig() {
		return currConfig;
	}

	/**
	 * Sets the path to the directory that hold serialized RunConfigDataNodes
	 * 
	 * @param path
	 *            The path we would to serialize the RunConfigDataNodes to
	 */
	public void setSerializePath(String path) {
		serializePath = path;
	}

	/**
	 * This function loads all of the serialized run configurations into a map
	 * for easy access.
	 */
	public void loadSavedConfigsMap() {
		final File folder = new File(serializePath);
		listFilesForFolder(folder);
	}

	/**
	 * Gets all of the files in a specific folder
	 * 
	 * @param folder
	 *            the folder to load files from
	 */
	public void listFilesForFolder(final File folder) {
		for (final File fileEntry : folder.listFiles()) {
			if (fileEntry.isDirectory()) {
				listFilesForFolder(fileEntry);
			} else if (!fileEntry.getName().startsWith(".")) {
				RunConfigDataNode temp = new RunConfigDataNode(null);
				temp.setName(fileEntry.getName());
				temp.setSerializeDestination(serializePath);
				String name = fileEntry.getName();
				if (!name.equals("entries")) {
					RunConfigDataNode config = temp.deserialize();
					if (!config.isMarkedForDelete()) {
						savedConfigs.put(name, config);
						newConfigsNum++;
					}
					// if the config is marked for delete, delete it.
					else {
						fileEntry.delete();
					}
				}
			}
		}
	}

	/**
	 * Creates the component map, which contains all {@link Component} in the
	 * GUI.
	 */
	private void createComponentMap(Component parent) {
		Component[] components = ((Container) parent).getComponents();
		for (int i = 0; i < components.length; i++) {
			if (componentMap.get(components[i].getName()) == null
					&& components[i].getName() != null)
				componentMap.put(components[i].getName(), components[i]);
			if (components[i] instanceof Container) {
				createComponentMap(components[i]);
			}
		}

	}

	/**
	 * Allows the user to get a specific {@link Component} by name.
	 * 
	 * @param name
	 *            The name of the {@link Component}
	 * @return The desired {@link Component}
	 */
	public Component getComponentByName(String name) {
		if (componentMap.containsKey(name)) {
			return componentMap.get(name);
		} else {
			System.out.println("Couldn't find " + name + " in map!");
			return null;
		}
	}

	/**
	 * Adds the specified {@link Component} to the componentMap.
	 * 
	 * @param comp
	 *            The {@link Component} to be added.
	 */
	public void addToMap(Component comp) {
		if (comp.getName() != null && comp.getName() != "")
			componentMap.put(comp.getName(), comp);
		else
			// TODO: maybe change this to a thrown exception
			System.out.println("component must have a name");
	}

	/**
	 * Gets the {@link CIVL_Command} associated with the input String, which
	 * represents a command name.
	 * 
	 * @param comName
	 *            The name of a command as a String
	 * @return The {@link CIVL_Command} with that name.
	 */
	public CIVL_Command getCommand(String comName) {
		CIVL_Command com = null;
		for (int i = 0; i < commands.length; i++) {
			if (commands[i].getName() == comName) {
				com = commands[i];
				break;
			}
		}
		return com;
	}

	/**
	 * Takes a VariableDeclarationNode and converts it into a CIVL_Input.
	 * 
	 * @param vdn
	 *            The VariableDeclarationNode to be converted
	 * @return The CIVL_Input that represents this vdn
	 */
	private CIVL_Input vdnToInput(VariableDeclarationNode vdn) {
		String name = vdn.getName();
		StringBuffer typeBuffer = vdn.getTypeNode().prettyRepresentation();
		String type = typeBuffer.toString();
		InitializerNode i = vdn.getInitializer();
		CIVL_Input ci = new CIVL_Input(name, type);

		if (i == null) {
			ci.setInitializer("");
		}

		else {
			String def = ((ConstantNode) i).getConstantValue().toString();
			ci.setInitializer(def);
		}

		return ci;
	}

	/**
	 * Gets the {@link TreePath} of a specified {@link DefaultMutableTreeNode}.
	 * 
	 * @param root
	 *            The root of the {@link JTree}.
	 * @param s
	 *            The string representation.
	 * @return The {@link TreePath} of the desired
	 *         {@link DefaultMutableTreeNode}.
	 */
	// Found at:
	// http://stackoverflow.com/questions/8210630/how-to-search-a-particular-node-in-jtree-and-make-that-node-expanded
	private TreePath getTreePath(DefaultMutableTreeNode root, String s) {
		@SuppressWarnings("unchecked")
		Enumeration<DefaultMutableTreeNode> e = root.depthFirstEnumeration();
		while (e.hasMoreElements()) {
			DefaultMutableTreeNode node = e.nextElement();
			if (node.toString().equalsIgnoreCase(s)) {
				return new TreePath(node.getPath());
			}
		}
		return null;
	}

	/**
	 * Converts a CommandName to a NormalCommandKind
	 * 
	 * @param name
	 *            the CommandName of the command
	 * @return The converted NormalCommandKind
	 */
	public NormalCommandKind comNameToComKind(CommandName name) {
		if (name.equals(CommandName.CONFIG)) {
			return NormalCommandKind.CONFIG;
		}

		else if (name.equals(CommandName.HELP)) {
			return NormalCommandKind.HELP;
		}

		else if (name.equals(CommandName.REPLAY)) {
			return NormalCommandKind.REPLAY;
		}

		else if (name.equals(CommandName.RUN)) {
			return NormalCommandKind.RUN;
		}

		else if (name.equals(CommandName.SHOW)) {
			return NormalCommandKind.SHOW;
		}

		else if (name.equals(CommandName.VERIFY)) {
			return NormalCommandKind.VERIFY;
		}

		else {
			return null;
		}
	}

	/**
	 * Creates a command line object that the GUI will use to run the
	 * configurations
	 * 
	 * @return The command line for the desired configuration
	 */
	public NormalCommandLine createNormalCommandLine() {
		Collection<String> files = new ArrayList<String>();

		NormalCommandLine line = new NormalCommandLine();
		if (currConfig != null) {
			if (!currConfig.getSelectedFiles().isEmpty()) {
				files.add(currConfig.getSelectedFiles().get(0).getPath());
				line.setFiles(files);
			}

			GMCSection cmdSection = currConfig.getGmcConfig()
					.getAnonymousSection();

			line.setGMCConfig(currConfig.getGmcConfig());
			line.setGMCSection(cmdSection);
			line.complete();
		}

		line.setCommand(comNameToComKind(currCommand));
		this.commandLine = line;
		return line;
	}

	public CompareCommandLine createCompareCommandLine() {
		Collection<String> files = new ArrayList<String>();
		files.add(currConfig.getSelectedFiles().get(0).getPath());
		NormalCommandLine line = new NormalCommandLine();
		GMCSection cmdSection = currConfig.getGmcConfig().getAnonymousSection();
		CommandName cmd = currCommand;
		line.setCommand(comNameToComKind(cmd));
		line.setFiles(files);
		line.setGMCConfig(currConfig.getGmcConfig());
		line.setGMCSection(cmdSection);

		line.complete();
		this.commandLine = line;
		return null;
	}

	/**
	 * Shows the options for the option table of the current run configuration.
	 */
	public void showOptions() {
		CIVLTable tbl_optionTable = (CIVLTable) getComponentByName("tbl_optionTable");
		DefaultTableModel optionModel = (DefaultTableModel) tbl_optionTable
				.getModel();

		if (optionModel.getRowCount() != 0) {
			optionModel.setRowCount(0);
			tbl_optionTable.clearSelection();
			tbl_optionTable.revalidate();
		}

		GMCSection section = currConfig.getGmcConfig().getSection(
				GMCConfiguration.ANONYMOUS_SECTION);
		Object[] opts;
		Collection<Option> options;
		if(currCommand.equals(CommandName.REPLAY)){
			options = CIVLCommand.getReplayOptions().values();
			opts = options.toArray();
		}
		else if(currCommand.equals(CommandName.VERIFY)){
			options= CIVLCommand.getVerifyOrCompareOptions().values();
			opts = options.toArray();
		}
		// Currently takes care of the run options
		else{
			options= CIVLCommand.getRunOptions().values();
			opts = options.toArray();
		}
//		else if(currCommand.equals(CommandName.RUN)){
//			options= CIVLCommand.getRunOptions().values();
//			opts = options.toArray();
//		}
//		else if(currCommand.equals(CommandName.COMPARE)){
//			
//		}
//		else if(currCommand.equals(CommandName.SHOW)){
//			
//		}
		Iterator<Option> iter_opt = options.iterator();
		List<Object> vals = new ArrayList<Object>();

		while (iter_opt.hasNext()) {
			Option curr = iter_opt.next();
			vals.add(section.getValueOrDefault(curr));
		}

		// Sets all of the default-ize buttons
		new ButtonColumn(tbl_optionTable, defaultize, 2);

		for (int i = 0; i < vals.size(); i++) {
			Option currOpt = (Option) opts[i];
			/*
			 * if (currOpt.name().equals("sysIncludePath")) {
			 * optionModel.addRow(new Object[] { currOpt, "sysIncludePath",
			 * "Default" }); }
			 * 
			 * else if (currOpt.name().equals("userIncludePath")) {
			 * optionModel.addRow(new Object[] { currOpt, "userIncludePath",
			 * "Default" }); }
			 */
			// else {
			optionModel
					.addRow(new Object[] { currOpt, vals.get(i), "Default" });
			// }
		}
	}

	/**
	 * Shows the inputs for the option table of the current run configuration.
	 */
	public void showInputs() {
		CIVLTable tbl_inputTable = (CIVLTable) getComponentByName("tbl_inputTable");
		DefaultTableModel inputModel = (DefaultTableModel) tbl_inputTable
				.getModel();

		if (inputModel.getRowCount() != 0) {
			inputModel.setRowCount(0);
			tbl_inputTable.clearSelection();
		}

		// GMCSection gmcs = currConfig.getGmcConfig().getAnonymousSection();
		ArrayList<CIVL_Input> inputList = currConfig.getInputs();
		for (int i = 0; i < inputList.size(); i++) {
			CIVL_Input input = inputList.get(i);
			inputModel.addRow(new Object[] { input.getName(), input.getType(),
					input.getValue(), input.getInitializer() });
		}

	}

	/**
	 * Shows the selected files for the option table of the current run
	 * configuration.
	 */
	public void showSelectedFiles() {
		CIVLTable tbl_fileTable = (CIVLTable) getComponentByName("tbl_fileTable");
		DefaultTableModel fileModel = (DefaultTableModel) tbl_fileTable
				.getModel();
		if (fileModel.getRowCount() != 0) {
			fileModel.setRowCount(0);
			tbl_fileTable.clearSelection();
		}

		ArrayList<File> files = currConfig.getSelectedFiles();
		for (int i = 0; i < files.size(); i++) {
			File f = files.get(i);
			fileModel
					.addRow(new Object[] { f.getName(), f.getPath(), "Delete" });
		}
	}

	/*
	 * Shows the console view upon execution
	 */
	public void showConsole(){
		if(lastRunCommand == null || lastRunCommand.equals(currCommand)){
			CIVLTable tbl_consoleTable = (CIVLTable) getComponentByName("tbl_consoleTable");
			DefaultTableModel consoleModel = (DefaultTableModel) tbl_consoleTable
					.getModel();
			
			if (consoleModel.getRowCount() != 0) {
				consoleModel.setRowCount(0);
				tbl_consoleTable.clearSelection();
			}
			tbl_consoleTable.clearSelection();
			if(consoleString != null){
				consoleModel.addRow(new Object[]{consoleString});
	//			consoleModel.addRow(new Object[]{" ", consoleStatsList.get(0), consoleStatsList.get(1), 
	//					consoleStatsList.get(2), consoleStatsList.get(3), consoleStatsList.get(4), 
	//					consoleStatsList.get(5), consoleStatsList.get(6), consoleStatsList.get(7),
	//					consoleStatsList.get(8)});
				tempString = consoleString;
	// if there are now rows, add the rows
	// otherwise, just replace current row with new values
				consoleModel.fireTableDataChanged();
				consoleModel.addRow(new Object[]{"command:", consoleStatsList.get(0)});
				consoleModel.addRow(new Object[]{"time:", consoleStatsList.get(1)});
				consoleModel.addRow(new Object[]{"memory:", consoleStatsList.get(2)});
				consoleModel.addRow(new Object[]{"max process:", consoleStatsList.get(3)});
				consoleModel.addRow(new Object[]{"states:", consoleStatsList.get(4)});
				consoleModel.addRow(new Object[]{"states saved", consoleStatsList.get(5)});
				if(!currCommand.equals(CommandName.REPLAY) && !currCommand.equals(CommandName.RUN)){
					consoleModel.addRow(new Object[]{"state matches", consoleStatsList.get(6)});
					consoleModel.addRow(new Object[]{"transitions", consoleStatsList.get(7)});
					consoleModel.addRow(new Object[]{"trace steps", consoleStatsList.get(8)});
					consoleModel.addRow(new Object[]{"valid calls", consoleStatsList.get(9)});
					consoleModel.addRow(new Object[]{"provers", consoleStatsList.get(10)});
					consoleModel.addRow(new Object[]{"prover calls", consoleStatsList.get(11)});
				}
				else if(currCommand.equals(CommandName.RUN)){
					consoleModel.addRow(new Object[]{"seed", consoleStatsList.get(6)});
					consoleModel.addRow(new Object[]{"valid calls", consoleStatsList.get(7)});
					consoleModel.addRow(new Object[]{"provers", consoleStatsList.get(8)});
					consoleModel.addRow(new Object[]{"prover calls", consoleStatsList.get(9)});
				}
				else{
					consoleModel.addRow(new Object[]{"valid calls", consoleStatsList.get(6)});
					consoleModel.addRow(new Object[]{"provers", consoleStatsList.get(7)});
					consoleModel.addRow(new Object[]{"prover calls", consoleStatsList.get(8)});
				}
			}
		}
//		JTextArea consoleOutput = new JTextArea();
//		consoleOutput.setText("Tester");
//		tbl_consoleTable.add(consoleOutput);
//		
	}
	
	public static void clearTable() {
		
	}
	
	/**
	 * Sets the options in the table when values are changed.
	 */
	@SuppressWarnings("unused")
	public void setOptions() {
		CIVLTable tbl_optionTable = (CIVLTable) getComponentByName("tbl_optionTable");
		DefaultTableModel optionModel = (DefaultTableModel) tbl_optionTable
				.getModel();

		Object[] opts;
		GMCSection section = currConfig.getGmcConfig().getAnonymousSection();

		Collection<Option> options;
		if(currCommand.equals(CommandName.REPLAY)){
			options = CIVLCommand.getReplayOptions().values();
			opts = options.toArray();
		}
		else if(currCommand.equals(CommandName.VERIFY)){
			options= CIVLCommand.getVerifyOrCompareOptions().values();
			opts = options.toArray();
		}
		// Currently takes care of the run options
		else{
			options= CIVLCommand.getRunOptions().values();
			opts = options.toArray();
		}
//		else if(currCommand.equals(CommandName.RUN)){
//			options= CIVLCommand.getRunOptions().values();
//			opts = options.toArray();
//		}
//		else if(currCommand.equals(CommandName.COMPARE)){
//			
//		}
//		else if(currCommand.equals(CommandName.SHOW)){
//			
//		}
		Iterator<Option> iter_opt = options.iterator();
		List<Object> vals = new ArrayList<Object>();

		for (int j = 0; j < optionModel.getRowCount(); j++) {
			vals.add(optionModel.getValueAt(j, 1));
		}

		for (int i = 0; i < vals.size(); i++) {
			Option currOpt = (Option) opts[i];
			Object val = vals.get(i);

			if (!currOpt.type().equals(OptionType.MAP)) {
				if (val instanceof String
						&& currOpt.type().equals(OptionType.INTEGER)) {
					Integer value = Integer.valueOf((String) val);
					section.setScalarValue(currOpt, value);
				}
				/*
				 * else if(val == null) { section.setScalarValue(currOpt, ""); }
				 */
				else if (true) {
					System.out.println("val: " + val);
				}
				section.setScalarValue(currOpt, val);
			}
		}
	}

	/**
	 * Sets the inputs based on the current RunConfiguration's selected file.
	 */
	public void setInputs() {
		CIVLTable tbl_inputTable = (CIVLTable) getComponentByName("tbl_inputTable");
		DefaultTableModel inputModel = (DefaultTableModel) tbl_inputTable
				.getModel();
		ArrayList<CIVL_Input> inputList = currConfig.getInputs();
		inputList.clear();
		GMCSection gmcs = currConfig.getGmcConfig().getAnonymousSection();
		for (int j = 0; j < inputModel.getRowCount(); j++) {
			String name = (String) inputModel.getValueAt(j, 0);
			String type = inputModel.getValueAt(j, 1).toString();
			Object value = inputModel.getValueAt(j, 2);
			String init = "";

			if (inputModel.getValueAt(j, 3) != null) {
				init = inputModel.getValueAt(j, 3).toString();
			}

			CIVL_Input input = new CIVL_Input(name, type);
			input.setValue(value);
			input.setInitializer(init);
			inputList.add(input);

			// Add the inputs to the value map in GMCSection
			if (!value.toString().equals("")) {
				gmcs.putMapEntry(CIVLConstants.inputO, input.getName(),
						input.getValue());
			}
		}

	}

	/**
	 * Sets the selected files based on what files have been chosen for the
	 * given RunConfigurationDataNode.
	 * 
	 * @param the
	 *            row the delete occurs in
	 */
	public void deleteSelectedFile(int row) {
		ArrayList<File> files = currConfig.getSelectedFiles();
		files.remove(row);
	}

	/**
	 * Saves the sysPathString or userPathString.
	 * 
	 * @param value
	 *            the path string set by the user in PathChooser
	 * @param optName
	 *            Either sysPathString or userPathString
	 */
	public void save(String value, String optName) {
		Option option = currConfig.getGmcConfig().getOption(optName);
		GMCSection section = currConfig.getGmcConfig().getSection(
				GMCConfiguration.ANONYMOUS_SECTION);
		section.setScalarValue(option, value);

	}

	/**
	 * Sets the columns' width in the given table to size
	 * 
	 * @param tbl
	 *            The CIVLTable containing the columns
	 * @param size
	 *            The new size for the columns
	 * 
	 * @param col
	 *            The column(by index) we are resizing
	 */
	public void setColumnSize(CIVLTable tbl, int size, int col) {
		TableColumnModel tcm = tbl.getColumnModel();
		tcm.getColumn(col).setMaxWidth(size);
		tcm.getColumn(col).setMinWidth(size);
	}

	/**
	 * Draws the view for the selected {@link RunConfigDataNode}.
	 */
	public void drawView() {
		JPanel p_view = (JPanel) getComponentByName("p_view");
		JPanel p_info = (JPanel) getComponentByName("p_info");
		JPanel p_chooseFile = (JPanel) getComponentByName("p_chooseFile");
		JPanel p_options = (JPanel) getComponentByName("p_options");
		JPanel p_inputs = (JPanel) getComponentByName("p_inputs");
		JPanel p_console = (JPanel) getComponentByName("p_console");
		JTabbedPane tp_commandView = (JTabbedPane) getComponentByName("tp_commandView");
		JTextField tf_chooseFile = (JTextField) getComponentByName("tf_chooseFile");
		if (currConfig != null) {
			p_view.removeAll();
			p_view.validate();
			tp_commandView.removeAll();
			tp_commandView.validate();

			if (currConfig.getSelectedFile() != null) {
				tf_chooseFile.setText(currConfig.getSelectedFile().getName());
			} else
				tf_chooseFile.setText("");

			NormalCommandKind currCommand = currConfig.getNormalCommandKind();
			// CONFIG, SHOW, VERIFY, REPLAY, GUI, HELP, RUN
			if (currCommand.equals(NormalCommandKind.CONFIG)) {
				tp_commandView.addTab("Choose File", p_chooseFile);
				p_view.add(tp_commandView);
				p_view.validate();

			} else if (currCommand.equals(NormalCommandKind.GUI)) {
				tp_commandView.addTab("Choose File", p_chooseFile);
				p_view.add(tp_commandView);
				p_view.validate();

			} else if (currCommand.equals(NormalCommandKind.HELP)) {
				tp_commandView.addTab("Choose File", p_chooseFile);
				p_view.add(tp_commandView);
				p_view.validate();

			} else if (currCommand.equals(NormalCommandKind.REPLAY)) {
				tp_commandView.addTab("Choose File", p_chooseFile);
				tp_commandView.addTab("Options", p_options);
				tp_commandView.addTab("Console", p_console);
				showOptions();
				showConsole();
				showSelectedFiles();
				p_view.add(tp_commandView);
				p_view.validate();

			} else if (currCommand.equals(NormalCommandKind.SHOW)) {
				tp_commandView.addTab("Choose File", p_chooseFile);
				tp_commandView.addTab("Options", p_options);
				tp_commandView.addTab("Inputs", p_inputs);
				tp_commandView.addTab("Console", p_console);
				p_view.add(tp_commandView);
				showOptions();
				showConsole();
				showSelectedFiles();
				showSelectedFiles();
				p_view.validate();

			} else if (currCommand.equals(NormalCommandKind.RUN)) {
				tp_commandView.addTab("Choose File", p_chooseFile);
				tp_commandView.addTab("Options", p_options);
				tp_commandView.addTab("Inputs", p_inputs);
				tp_commandView.addTab("Console", p_console);
				p_view.add(tp_commandView);
				showOptions();
				showInputs();
				showConsole();
				showSelectedFiles();
				p_view.validate();

			} else if (currCommand.equals(NormalCommandKind.VERIFY)) {
				tp_commandView.addTab("Choose File", p_chooseFile);
				tp_commandView.addTab("Options", p_options);
				tp_commandView.addTab("Inputs", p_inputs);
				tp_commandView.addTab("Console", p_console);
				showOptions();
				showInputs();
				showConsole();
				showSelectedFiles();
				p_view.add(tp_commandView);
				p_view.validate();
			}

		}

		else {
			p_view.removeAll();
			p_view.validate();
			p_view.add(p_info);
			p_view.validate();
		}
	}

	/**
	 * Creates the command {@link JPanel}.
	 */
	public void initCommandsPanel() {
		JPanel p_commands = new JPanel();
		JButton bt_new = new JButton("");
		JButton bt_duplicate = new JButton("");
		JButton bt_deleteConfig = new JButton("");
		DefaultMutableTreeNode top = initNodes();
		JTree jt_commands = new JTree(top);
		JPanel p_tree = new JPanel();
		JPanel p_buttons = new JPanel();

		p_commands.setName("p_commands");
		bt_new.setName("bt_new");
		bt_duplicate.setName("bt_duplicate");
		bt_deleteConfig.setName("bt_deleteConfig");
		jt_commands.setName("jt_commands");
		p_tree.setName("p_tree");
		p_buttons.setName("p_buttons");

		bt_deleteConfig.setIcon(new ImageIcon("Images/delete.png"));
		bt_new.setIcon(new ImageIcon("Images/new.png"));
		bt_duplicate.setIcon(new ImageIcon("Images/duplicate.png"));

		bt_deleteConfig.setEnabled(false);
		bt_duplicate.setEnabled(false);

		p_tree.setLayout(null);

		jt_commands.setBounds(6, 6, 199, 548);
		p_tree.add(jt_commands);
		p_buttons.add(bt_new);
		p_buttons.add(bt_duplicate);
		p_buttons.add(bt_deleteConfig);
		p_commands.add(p_buttons);
		p_commands.add(p_tree);

		add(p_commands);
		revalidate();
		repaint();
	}

	/**
	 * Creates the container {@link JPanel}.
	 */
	@SuppressWarnings("deprecation")
	public void initContainer() {
		JPanel p_container = new JPanel();
		JPanel p_view = new JPanel();
		JPanel p_info = new JPanel();
		JPanel p_chooseFile = new JPanel();
		JPanel p_options = new JPanel();
		JPanel p_console = new JPanel();
		JPanel p_inputs = new JPanel();

		JScrollPane sp_optionTable = new JScrollPane();
		JScrollPane sp_inputTable = new JScrollPane();
		JScrollPane sp_fileTable = new JScrollPane();
		JScrollPane sp_consoleTable = new JScrollPane();

		JTabbedPane tp_commandView = new JTabbedPane();

		JButton bt_revert = new JButton("Revert");
		JButton bt_apply = new JButton("Apply");
		JButton bt_browseFile = new JButton("Browse...");

		bt_revert.hide();

		JLabel lb_name = new JLabel("Name: ");
		JLabel lb_new = new JLabel(
				"New - Press the 'new' button to create a new run configuration of the selected type.");
		JLabel lb_duplicate = new JLabel(
				"Duplicate - Press the 'duplicate' button to duplicate the current run configuration.");
		JLabel lb_delete = new JLabel(
				"Delete - Press the 'delete' button to delete the currently selected run configuration.");
		lb_new.setIcon(new ImageIcon("Images/new.png"));
		lb_duplicate.setIcon(new ImageIcon("Images/duplicate.png"));
		lb_delete.setIcon(new ImageIcon("Images/delete.png"));

		JTextField tf_name = new JTextField();
		JTextField tf_chooseFile = new JTextField();

		JTable tbl_optionTable = new CIVLTable(new int[] { 1, 2 }, "option",
				this);
		final JTable tbl_inputTable = new CIVLTable(new int[] { 2 }, "input",
				this);
		final JTable tbl_fileTable = new CIVLTable(new int[] { 2 }, "file",
				this);
		
		final JTable tbl_consoleTable = new CIVLTable(new int[] { 1 }, "console",
				this);
		
		
		

		tbl_optionTable.putClientProperty("terminateEditOnFocusLost",
				Boolean.TRUE);

		tf_chooseFile.setColumns(58);
		tf_name.setColumns(10);

		p_options.setLayout(new BorderLayout(0, 0));
		p_inputs.setLayout(new BorderLayout(0, 0));
		p_console.setLayout(new BorderLayout(0, 0));

		p_container.setName("p_container");
		p_view.setName("p_view");
		p_info.setName("p_info");
		p_chooseFile.setName("p_chooseFile");
		p_options.setName("p_options");
		p_console.setName("p_console");
		p_inputs.setName("p_inputs");
		sp_optionTable.setName("sp_optionTable");
		sp_inputTable.setName("sp_inputTable");
		sp_fileTable.setName("sp_fileTable");
		sp_consoleTable.setName("sp_consoleTable");
		tp_commandView.setName("tp_commandView");
		bt_revert.setName("bt_revert");
		bt_apply.setName("bt_apply");
		bt_browseFile.setName("bt_browseFile");
		tf_name.setName("tf_name");
		tf_chooseFile.setName("tf_chooseFile");
		lb_name.setName("lb_name");
		tbl_optionTable.setName("tbl_optionTable");
		tbl_inputTable.setName("tbl_inputTable");
		tbl_fileTable.setName("tbl_fileTable");
		tbl_consoleTable.setName("tbl_consoleTable");

		lb_new.setBounds(6, 6, 554, 16);
		lb_duplicate.setBounds(6, 39, 589, 16);
		lb_delete.setBounds(6, 72, 589, 16);

		sp_optionTable.setViewportView(tbl_optionTable);
		sp_inputTable.setViewportView(tbl_inputTable);
		sp_fileTable.setViewportView(tbl_fileTable);
		sp_consoleTable.setViewportView(tbl_consoleTable);

		tbl_optionTable.setModel(new DefaultTableModel(null, new String[] {
				"Option", "Value", "Default" }));
		tbl_inputTable.setModel(new DefaultTableModel(null, new String[] {
				"Variable", "Type", "Value", "Default" }));
		tbl_fileTable.setModel(new DefaultTableModel(null, new String[] {
				"File Name", "File Path", "Delete" }));
//		tbl_consoleTable.setModel(new DefaultTableModel(null, new String[] {"Results", "command", "time(s)", "memory(bytes)", "max process count", "states", "states saved", "state matches", "transitions", "trace steps" }));
		tbl_consoleTable.setModel(new DefaultTableModel(null, new String[] {"Results", "Statistics"}));
//		tbl_statistics.setModel(new DefaultTableModel(null, new String[] {"hey"}));
		
		tbl_optionTable.setCellSelectionEnabled(true);
		tbl_inputTable.setCellSelectionEnabled(true);
		tbl_fileTable.setCellSelectionEnabled(true);
		tbl_consoleTable.setCellSelectionEnabled(true);

		tbl_optionTable.setShowGrid(true);
		tbl_optionTable.setGridColor(Color.BLUE);

		//TODO: Investigate rows for different views
		tbl_optionTable.setRowHeight(35);
		tbl_inputTable.setRowHeight(35);
		tbl_fileTable.setRowHeight(35);
		tbl_fileTable.setRowHeight(35);

		setColumnSize((CIVLTable) tbl_optionTable, 215, 0);
		setColumnSize((CIVLTable) tbl_optionTable, 215, 1);
		setColumnSize((CIVLTable) tbl_optionTable, 105, 2);

		tf_name.setEnabled(false);
		bt_apply.setEnabled(false);

		tbl_fileTable.getModel().addTableModelListener(
				new TableModelListener() {

					/**
					 * Deletes the file from the selected files list for the
					 * current config
					 */
					@Override
					public void tableChanged(TableModelEvent e) {
						if (currConfig != null) {
							if (((CIVLTable) tbl_fileTable).deleting
									&& e.getType() == TableModelEvent.DELETE) {
								deleteSelectedFile(e.getLastRow());

								DefaultTableModel inputModel = (DefaultTableModel) tbl_inputTable
										.getModel();

								if (inputModel.getRowCount() != 0) {
									inputModel.setRowCount(0);
									tbl_inputTable.clearSelection();
									tbl_inputTable.revalidate();
								}
							}
						}
					}

				});

		p_container.add(p_view);
		p_container.add(bt_revert);
		p_container.add(bt_apply);
		p_container.add(tf_name);
		p_container.add(lb_name);

		p_info.add(lb_new);
		p_info.add(lb_duplicate);
		p_info.add(lb_delete);

		// p_chooseFile.add(lb_chooseFile);
		// p_chooseFile.add(tf_chooseFile);
		p_chooseFile.add(bt_browseFile);
		p_chooseFile.add(sp_fileTable);

		p_options.add(sp_optionTable);
		p_inputs.add(sp_inputTable);
		p_console.add(sp_consoleTable);

		addToMap(p_info);
		addToMap(tp_commandView);
		addToMap(p_chooseFile);
		addToMap(p_options);
		addToMap(p_console);
		addToMap(p_inputs);
		addToMap(bt_browseFile);
		addToMap(tf_chooseFile);
		addToMap(sp_optionTable);
		addToMap(sp_inputTable);
		addToMap(sp_fileTable);
		addToMap(sp_consoleTable);
		addToMap(tbl_optionTable);
		addToMap(tbl_inputTable);
		addToMap(tbl_fileTable);
		addToMap(tbl_consoleTable);
		add(p_container);

		revalidate();
		repaint();
	}

	/**
	 * Creates the execute {@link JPanel}.
	 */
	public void initExecute() {
		JPanel p_execute = new JPanel();
		JButton bt_help = new JButton("Help");
		JButton bt_cancel = new JButton("Cancel");
		JButton bt_run = new JButton("Run");

		bt_run.setEnabled(false);

		p_execute.setName("p_execute");
		bt_help.setName("bt_help");
		bt_cancel.setName("bt_cancel");
		bt_run.setName("bt_run");

		p_execute.add(bt_help);
		p_execute.add(bt_cancel);
		p_execute.add(bt_run);

		add(p_execute);
		revalidate();
		repaint();
	}

	/**
	 * Creates the header {@link JPanel}.
	 */
	public void initHeader() {
		JPanel p_header = new JPanel();
		JLabel lb_icon = new JLabel("");
		JTextArea ta_header = new JTextArea();

		p_header.setName("p_header");
		lb_icon.setName("lb_icon");
		ta_header.setName("ta_header");

		p_header.setBackground(Color.WHITE);
		ta_header.setFont(new Font("Lucida Grande", Font.PLAIN, 13));
		ta_header.setFocusable(false);
		ta_header.setDragEnabled(false);
		ta_header.setText("  Create, manage and run configurations\n"
				+ "  Choose a Command");

		lb_icon.setIcon(new ImageIcon("Images/logo.png"));

		
		p_header.add(ta_header);
		p_header.add(lb_icon);

		add(p_header);
		revalidate();
		repaint();
	}

	/**
	 * Creates all of the the {@link DefaultMutableTreeNode} that will be used
	 * for the {@link JTree}, jt_commands.
	 * This creates the initial view and where all of the command options are shown.
	 * 
	 * @return The node that will be the root of jt_commands
	 */
	public DefaultMutableTreeNode initNodes() {
		DefaultMutableTreeNode top = new DefaultMutableTreeNode("commands");

		Collection<RunConfigDataNode> c = savedConfigs.values();

		Object[] configs = c.toArray();
		Object[] vals = CommandName.values();

		for (int i = 0; i < vals.length; i++) {
			String nodeName = vals[i].toString();

			// Comment some of this conditional as features become added. This
			// stops them from showing in the tree until they work correctly
			if (!nodeName.equals("HELP") && !nodeName.equals("CONFIG")
					&& !nodeName.equals("GUI") && !nodeName.equals("COMPARE")
					&& !nodeName.equals("COMPARE_REPLAY")

					//&& !nodeName.equals("REPLAY")
					&& !nodeName.equals("SHOW")) {
				CommandNode node = new CommandNode(nodeName,
						(CommandName) vals[i]);
				top.add(node);
			}
		}

		for (int i = 0; i < configs.length; i++) {
			RunConfigDataNode curr = (RunConfigDataNode) configs[i];

			if (curr.comLine.commandLineKind() == CommandLineKind.COMPARE) {
				CommandNode node;
				while (top.children().hasMoreElements()) {
					Object currNode = top.children().nextElement();
					node = (CommandNode) currNode;
					if (node.commandName == CommandName.COMPARE) {
						node.add(curr);
					}
				}
			}

			else if (curr.comLine.commandLineKind() == CommandLineKind.NORMAL) {
				CommandNode node;
				@SuppressWarnings("unchecked")
				Enumeration<CommandNode> e = top.children();
				while (e.hasMoreElements()) {
					Object currNode = e.nextElement();
					node = (CommandNode) currNode;
					if (comNameToComKind(node.commandName) == curr
							.getNormalCommandKind()) {
						node.add(curr);
						break;
					}
				}
			}
		}

		return top;
	}

	/**
	 * Creates the listeners for the various {@link Component} in the GUI.
	 */
	@SuppressWarnings("serial")
	public void initListeners(final GUI_revamp gui) {
		final JTree jt_commands = (JTree) getComponentByName("jt_commands");
		final JTextArea ta_header = (JTextArea) getComponentByName("ta_header");
		final JButton bt_new = (JButton) getComponentByName("bt_new");
		final JButton bt_help = (JButton) getComponentByName("bt_help");
		final JButton bt_cancel = (JButton) getComponentByName("bt_cancel");
		final JButton bt_run = (JButton) getComponentByName("bt_run");
		final JButton bt_apply = (JButton) getComponentByName("bt_apply");
		final JButton bt_browseFile = (JButton) getComponentByName("bt_browseFile");
		final JButton bt_deleteConfig = (JButton) getComponentByName("bt_deleteConfig");
		final JButton bt_duplicate = (JButton) getComponentByName("bt_duplicate");
		final JTabbedPane tp_commandView = (JTabbedPane) getComponentByName("tp_commandView");
		final JTextField tf_name = (JTextField) getComponentByName("tf_name");
		final JTextField tf_chooseFile = (JTextField) getComponentByName("tf_chooseFile");
		final CIVLTable tbl_optionTable = (CIVLTable) getComponentByName("tbl_optionTable");
		final CIVLTable tbl_fileTable = (CIVLTable) getComponentByName("tbl_fileTable");
		final CIVLTable tbl_inputTable = (CIVLTable) getComponentByName("tbl_inputTable");

		/**
		 * Tree Selection Listener
		 */
		jt_commands.setExpandsSelectedPaths(true);
		jt_commands.addTreeSelectionListener(new TreeSelectionListener() {
			@SuppressWarnings("unused")
			public void valueChanged(TreeSelectionEvent e) {
				String headerText = "  Create, manage and run configurations\n";
				TreePath selected = jt_commands.getSelectionPath();
				DefaultMutableTreeNode node = (DefaultMutableTreeNode) jt_commands
						.getLastSelectedPathComponent();

				// To be implemented when we want a dialogue box that asks if
				// you want to
				// Save a run Configuration
				/*
				 * if (currConfig != null) { if (!currConfig.applyClicked &&
				 * !currConfig.isBrandNew()) { String message =
				 * "Do you want to save your run Configuration?"; int answer =
				 * JOptionPane .showConfirmDialog(gui, message);
				 * 
				 * if (answer == JOptionPane.CANCEL_OPTION) {
				 * 
				 * }
				 * 
				 * else if (answer == JOptionPane.NO_OPTION) {
				 * 
				 * }
				 * 
				 * else if (answer == JOptionPane.YES_OPTION) { if (currConfig
				 * != null) { currConfig.applyClicked = true; setOptions();
				 * setInputs(); currConfig.setUserObject(currConfig.getName());
				 * revalidate(); repaint(); currConfig.serialize(); } } } }
				 */

				if (selected == null) {
					System.out.println("Node no longer exists");
				}

				// Head node of tree
				else if (selected.getPathCount() == 1) {
					currConfig = null;
					tf_name.setEnabled(false);
					bt_run.setEnabled(false);
					bt_apply.setEnabled(false);
					bt_deleteConfig.setEnabled(false);
					bt_duplicate.setEnabled(false);
					tf_name.setText("");
					drawView();
					repaint();
				}

				// Command Level Nodes(i.e RUN, VERIFY etc.)
				else if (selected.getPathCount() == 2) {
					tf_name.setEnabled(false);
					bt_run.setEnabled(false);
					bt_apply.setEnabled(false);
					bt_deleteConfig.setEnabled(false);
					bt_duplicate.setEnabled(false);

					currConfig = null;
					currCommand = ((CommandNode) node).commandName;

					drawView();
					tf_name.setText("");
					headerText += "  " + node.toString();
					ta_header.setText(headerText);
				}

				// Configuration Level Nodes(i.e New Configuration(0))
				else if (selected.getPathCount() == 3) {
					DefaultTableModel currOptModel = (DefaultTableModel) tbl_optionTable
							.getModel();

					tf_name.setEnabled(true);
					bt_run.setEnabled(true);
					bt_apply.setEnabled(true);
					bt_deleteConfig.setEnabled(true);
					bt_duplicate.setEnabled(true);

					if (currConfig == null) {
						currConfig = (RunConfigDataNode) node;
						currConfig.setBrandNew(false);
						currCommand = ((CommandNode) currConfig.getParent()).commandName;
						tf_name.setText(currConfig.getName());
						drawView();
					}

					else {
						if (tbl_optionTable.isEditing()) {
							tbl_optionTable.getCellEditor().stopCellEditing();
						}
						currConfig.applyClicked = false;
						currConfig = (RunConfigDataNode) node;
						currCommand = ((CommandNode) currConfig.getParent()).commandName;
						currConfig.setBrandNew(false);
						tf_name.setText(currConfig.getName());
						drawView();
					}

				} else {
					ta_header.setText(headerText + "  Choose a Command");
					tf_name.setText("");
				}

				revalidate();
				repaint();
			}
		});

		/**
		 * Browse File Listener
		 */
		ActionListener browseFile = new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				File start = new File(examplesPath);
				final JFileChooser chooser = new JFileChooser();				
				chooser.setCurrentDirectory(start);
				FileNameExtensionFilter filter = new FileNameExtensionFilter(
						"CIVL Files (.cvl, .c, .cuda)", "cvl", "c", "cuda");
				chooser.setFileFilter(filter);
				final DefaultTableModel currFileModel = (DefaultTableModel) tbl_fileTable
						.getModel();
				final DefaultTableModel currInputModel = (DefaultTableModel) tbl_inputTable
						.getModel();

				chooser.addActionListener(new ActionListener() {
					public void actionPerformed(ActionEvent e) {
						examplesPath = chooser.getCurrentDirectory().getPath();
						File selectedFile = chooser.getSelectedFile();
						// currConfig.setSelectedFile(selectedFile);
						currConfig.getSelectedFiles().add(selectedFile);
						currFileModel.addRow(new Object[] {
								selectedFile.getName(), selectedFile.getPath(),
								"Delete" });

						tf_chooseFile.setText(selectedFile.getName());
						Object[] files = currConfig.getSelectedFiles()
								.toArray();
						String[] filePaths = new String[files.length];
						for (int i = 0; i < files.length; i++) {
							filePaths[i] = ((File) files[i]).getPath();
						}
						UserInterface ui = new UserInterface();
						List<VariableDeclarationNode> inputs = ui
								.getInputVariables(filePaths);

						ArrayList<CIVL_Input> inputList = currConfig
								.getInputs();

						for (int j = 0; j < inputs.size(); j++) {
							VariableDeclarationNode vdn = inputs.get(j);
							CIVL_Input ci = vdnToInput(vdn);
							inputList.add(ci);
							currInputModel.addRow(new Object[] { vdn.getName(),
									vdn.getTypeNode().prettyRepresentation(),
									"", ci.getInitializer() });

						}

					}
				});
				chooser.showOpenDialog(null);
			}
		};

		bt_browseFile.addActionListener(browseFile);

		/**
		 * The action that sets values to their default values
		 */
		defaultize = new AbstractAction() {

			public void actionPerformed(ActionEvent e) {

				DefaultTableModel currOptModel = (DefaultTableModel) tbl_optionTable
						.getModel();

				int modelRow = tbl_optionTable.getSelectedRow();
				Object valToDefault = currOptModel.getValueAt(modelRow, 1);
				Option optToDefault = (Option) currOptModel.getValueAt(
						modelRow, 0);

				if (valToDefault instanceof Boolean) {
					Boolean defValue = (Boolean) optToDefault.defaultValue();

					// MAIN DEFAULT ACTION:
					tbl_optionTable.setValueAt(defValue, modelRow, 1);
				}

				else
					currOptModel.setValueAt(optToDefault.defaultValue(),
							modelRow, 1);
				repaint();
			}
		};

		/**
		 * Applies the changes to the RunConfigDataNode and serializes it.
		 */
		ActionListener apply = new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				if (currConfig != null) {
					currConfig.applyClicked = true;
					setOptions();
					setInputs();
					currConfig.setUserObject(currConfig.getName());
					revalidate();
					repaint();
					currConfig.serialize();
				}
			}
		};

		bt_apply.addActionListener(apply);

		/**
		 * Runs the GUI
		 */
		ActionListener run = new ActionListener() {
			@SuppressWarnings("unused")
			public void actionPerformed(ActionEvent e) {
				if (currConfig.getSelectedFiles().size() == 0) {
					JOptionPane
							.showMessageDialog(gui,
									"You must select a file before you run the configuration");
				}

				else {
					UserInterface ui = new UserInterface();

					setOptions();
					if (currCommand.equals(CommandName.COMPARE)
							|| currCommand.equals(CommandName.COMPARE_REPLAY)) {
						currConfig.comLine = createCompareCommandLine();
					} else {
						currConfig.comLine = createNormalCommandLine();
					}

					Collection<String> files = new ArrayList<String>();
					files.add(currConfig.getSelectedFiles().get(0).getName());

					currConfig.comLine.setGMCConfig(currConfig.getGmcConfig());

					GMCSection section = currConfig.getGmcConfig().getSection(
							GMCConfiguration.ANONYMOUS_SECTION);

					Option option = currConfig.getGmcConfig().getOption(
							"showProgram");

					// System.out.println(currConfig.comLine.gmcConfig().getAnonymousSection().getValue(option));
					currConfig.comLine.setGMCConfig(currConfig.getGmcConfig());

					String com = currCommand.name().toLowerCase();
					com += " ";
					com += currConfig.getSelectedFiles().get(0).getName();
					currConfig.comLine.setCommandString(com);

					try {
						boolean result = ui.runNormalCommand((NormalCommandLine) currConfig.comLine);
						if(currCommand.equals(CommandName.REPLAY)){
							int n = JOptionPane.showConfirmDialog(gui, "Do you wish to run the Trace Viewer?", "Trace Viewer", JOptionPane.YES_NO_OPTION);
							if(n==0){
								TraceViewer viewer = new TraceViewer(ui.getTrace(), ui.getAnalyzer());
							}
						}
						consoleString = ui.consoleString;
						consoleStatsList = ui.consoleStatsList;
						lastRunCommand = currCommand;
						showConsole();
						if(currCommand.equals(CommandName.REPLAY)){
							tp_commandView.setSelectedIndex(2);
						}
						else{
							tp_commandView.setSelectedIndex(3);
						} 
							//Console gets drawn here
					} catch (CommandLineException | ABCException | IOException
							| MisguidedExecutionException | SvcompException e1) {
						e1.printStackTrace();
					}
				}
			}
		};

		bt_run.addActionListener(run);

		/**
		 * The Delete Config ActionListener
		 */
		ActionListener delete = new ActionListener() {
			@SuppressWarnings("unused")
			public void actionPerformed(ActionEvent e) {
				DefaultTableModel currOptModel = (DefaultTableModel) tbl_optionTable
						.getModel();

				// File folder = new File(serializePath);
				// savedConfigs.remove(currConfig.getName());
				DefaultTreeModel model = (DefaultTreeModel) jt_commands
						.getModel();
				TreePath[] paths = jt_commands.getSelectionPaths();
				for (TreePath path : paths) {
					DefaultMutableTreeNode node = (DefaultMutableTreeNode) path
							.getLastPathComponent();
					if (node.getParent() != null) {
						model.removeNodeFromParent(node);
						File configToDelete = new File(serializePath
								+ currConfig.getName());
						configToDelete.delete();
						currConfig.deleteConfig();
						savedConfigs.remove(currConfig.getName());
						currConfig.serialize();
					}
				}
				currConfig = null;
				jt_commands.setSelectionRow(0);
				revalidate();
				repaint();
			}
		};

		bt_deleteConfig.addActionListener(delete);

		/**
		 * The new configuration ActionListener
		 */
		ActionListener newConfig = new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				DefaultTreeModel treeModel = (DefaultTreeModel) jt_commands
						.getModel();
				Object config = savedConfigs.get(tf_name.getText());
				boolean dontCreate = false;
				@SuppressWarnings("unused")
				DefaultMutableTreeNode node = (DefaultMutableTreeNode) jt_commands
						.getLastSelectedPathComponent();

				if (config != null) {
					dontCreate = true;
				}

				if (!dontCreate) {
					TreePath selected = jt_commands.getSelectionPath();

					DefaultMutableTreeNode selectedNode = (DefaultMutableTreeNode) jt_commands
							.getLastSelectedPathComponent();

					DefaultMutableTreeNode newChild = null;
					if (currCommand.equals(CommandName.COMPARE)
							|| currCommand.equals(CommandName.COMPARE_REPLAY)) {
						newChild = new RunConfigDataNode(
								createCompareCommandLine());
					} else {
						newChild = new RunConfigDataNode(
								createNormalCommandLine());
					}

					String newName = tf_name.getText();
					if (tf_name.getText().equals(null)
							|| tf_name.getText().equals("")) {
						newName = "New Configuration(" + newConfigsNum + ")";
						if (selected.getPathCount() == 2) {
							newConfigsNum++;
						}
					}

					if (savedConfigs.containsKey(newName)) {
						dontCreate = true;

					}

					if (dontCreate) {
					}

					else {
						newChild.setUserObject(newName);
						currConfig = (RunConfigDataNode) newChild;
						currConfig.setName(newName);
						((RunConfigDataNode) currConfig)
								.setSerializeDestination(serializePath);

						savedConfigs.put(currConfig.getName(), currConfig);

						if (selected.getPathCount() != 1)
							tf_name.setText(newName);

						if (selected.getPathCount() == 2) {
							((DefaultTreeModel) jt_commands.getModel())
									.insertNodeInto(currConfig, selectedNode,
											selectedNode.getChildCount());

							TreePath currPath = getTreePath(
									(DefaultMutableTreeNode) treeModel
											.getRoot(),
									currConfig.toString());
							jt_commands.setSelectionPath(currPath);

						}
					}
				}
				dontCreate = false;

			}
		};
		bt_new.addActionListener(newConfig);

		/**
		 * The action for duplicating a configuration
		 */
		ActionListener duplicate = new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				// TODO: find a way to DEEP copy a RunConfigDataNode
			}
		};

		bt_duplicate.addActionListener(duplicate);

		ActionListener help =  new ActionListener(){
			public void actionPerformed(ActionEvent e) {
				String helpMenu = "\nIn this GUI, you can use CIVL to run and verify programs, as well as replay counterexamples.\n"
						+ "\nCommands:\n"
						+ "RUN — Runs a random simulation of the program. \n\n"
						+ "VERIFY — Runs a verification of the program, exploring all possible states for violations.\n\n"
						+ "REPLAY — Replays the minimal counterexample trace produced by the VERIFY command."
						+ "\n\nProgram Options:\n\n"
						+ "After selecting a command, you have multiple tabs to select options.\n\n"
						+ "Choose File: Choose the program you wish to run through the file browser.\n\n"
						+ "Options: Select from the various options CIVL provides for program functionality.\n\n"
						+ "Input: After file load, you can choose to provide values for the program's input variables.";
				
				JOptionPane.showMessageDialog(gui, "GUI Instructions: " + helpMenu);
			}
		};
		
		
		bt_help.addActionListener(help);
		
		ActionListener cancel = new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				System.exit(0);
			}
		};

		bt_cancel.addActionListener(cancel);

		/**
		 * Listener that detects when the user is editing the name of the run
		 * configuration
		 */
		tf_name.addFocusListener(new FocusListener() {

			@Override
			public void focusGained(FocusEvent e) {

			}

			@Override
			public void focusLost(FocusEvent e) {
				if (currConfig != null) {
					currConfig.setName(tf_name.getText());
					currConfig.setUserObject(currConfig.getName());
				}
			}

		});

		/**
		 * Listener that detects when the user is editing the name of the run
		 * configuration
		 */
		tf_name.getDocument().addDocumentListener(new DocumentListener() {

			@Override
			public void insertUpdate(DocumentEvent e) {
				if (currConfig != null) {
					currConfig.setName(tf_name.getText());
					currConfig.setUserObject(currConfig.getName());
				}
			}

			@Override
			public void removeUpdate(DocumentEvent e) {
				if (currConfig != null) {
					currConfig.setName(tf_name.getText());
					currConfig.setUserObject(currConfig.getName());
				}
			}

			@Override
			public void changedUpdate(DocumentEvent e) {
				if (currConfig != null) {
					currConfig.setName(tf_name.getText());
					currConfig.setUserObject(currConfig.getName());
				}
			}
		});
	}

	/**
	 * Sets up the layouts that will be used in the GUI.
	 * <p>
	 * 
	 * NOTE: The group layouts are automatically generated code from a GUI
	 * builder, if any changes to the layouts is to be made it is advisable that
	 * you re-create the layouts using the editor of your choice rather than
	 * manually editing the code below.
	 */
	public void initLayouts() {
		JPanel p_header = (JPanel) getComponentByName("p_header");
		JPanel p_container = (JPanel) getComponentByName("p_container");
		JPanel p_tree = (JPanel) getComponentByName("p_tree");
		JPanel p_commands = (JPanel) getComponentByName("p_commands");
		JPanel p_execute = (JPanel) getComponentByName("p_execute");
		JPanel p_buttons = (JPanel) getComponentByName("p_buttons");
		JPanel p_view = (JPanel) getComponentByName("p_view");
		JPanel p_info = (JPanel) getComponentByName("p_info");
		JPanel p_chooseFile = (JPanel) getComponentByName("p_chooseFile");
		JButton bt_apply = (JButton) getComponentByName("bt_apply");
		JButton bt_revert = (JButton) getComponentByName("bt_revert");
		JTextArea ta_header = (JTextArea) getComponentByName("ta_header");
		JLabel lb_icon = (JLabel) getComponentByName("lb_icon");
		JLabel lb_name = (JLabel) getComponentByName("lb_name");
		JTextField tf_name = (JTextField) getComponentByName("tf_name");

		Border etched = BorderFactory.createEtchedBorder(EtchedBorder.LOWERED);

		p_header.setBorder(etched);
		p_container.setBorder(etched);
		p_commands.setBorder(etched);
		// p_execute.setBorder(etched);
		// p_view.setBorder(etched);
		// p_buttons.setBorder(etched);

		p_buttons.setLayout(new FlowLayout(FlowLayout.LEFT, 25, 2));
		p_chooseFile.setLayout(new FlowLayout(FlowLayout.LEFT, 6, 1));
		p_view.setLayout(new BorderLayout(0, 0));
		p_info.setLayout(null);

		// GroupLayout for main JFrame
		// If you want to change this, use something like netbeans or read more
		// into group layouts
		GroupLayout groupLayout = new GroupLayout(getContentPane());
		groupLayout
				.setHorizontalGroup(groupLayout
						.createParallelGroup(Alignment.LEADING)
						.addGroup(
								groupLayout
										.createSequentialGroup()
										.addContainerGap()
										.addGroup(
												groupLayout
														.createParallelGroup(
																Alignment.LEADING)
														.addGroup(
																groupLayout
																		.createSequentialGroup()
																		.addComponent(
																				p_commands,
																				GroupLayout.PREFERRED_SIZE,
																				225,
																				GroupLayout.PREFERRED_SIZE)
																		.addPreferredGap(
																				ComponentPlacement.RELATED)
																		.addGroup(
																				groupLayout
																						.createParallelGroup(
																								Alignment.LEADING)
																						.addComponent(
																								p_execute,
																								GroupLayout.DEFAULT_SIZE,
																								957,
																								Short.MAX_VALUE)
																						.addComponent(
																								p_container,
																								GroupLayout.DEFAULT_SIZE,
																								957,
																								Short.MAX_VALUE)))
														.addComponent(
																p_header,
																GroupLayout.DEFAULT_SIZE,
																1188,
																Short.MAX_VALUE))
										.addContainerGap()));
		groupLayout
				.setVerticalGroup(groupLayout
						.createParallelGroup(Alignment.LEADING)
						.addGroup(
								groupLayout
										.createSequentialGroup()
										.addContainerGap()
										.addComponent(p_header,
												GroupLayout.PREFERRED_SIZE, 57,
												GroupLayout.PREFERRED_SIZE)
										.addPreferredGap(
												ComponentPlacement.RELATED)
										.addGroup(
												groupLayout
														.createParallelGroup(
																Alignment.LEADING)
														.addComponent(
																p_commands,
																GroupLayout.DEFAULT_SIZE,
																603,
																Short.MAX_VALUE)
														.addGroup(
																groupLayout
																		.createSequentialGroup()
																		.addComponent(
																				p_container,
																				GroupLayout.PREFERRED_SIZE,
																				549,
																				GroupLayout.PREFERRED_SIZE)
																		.addPreferredGap(
																				ComponentPlacement.RELATED)
																		.addComponent(
																				p_execute,
																				GroupLayout.DEFAULT_SIZE,
																				48,
																				Short.MAX_VALUE)))
										.addContainerGap()));

		GroupLayout gl_p_container = new GroupLayout(p_container);
		gl_p_container
				.setHorizontalGroup(gl_p_container
						.createParallelGroup(Alignment.TRAILING)
						.addGroup(
								gl_p_container
										.createSequentialGroup()
										.addContainerGap()
										.addGroup(
												gl_p_container
														.createParallelGroup(
																Alignment.LEADING)
														.addComponent(
																p_view,
																GroupLayout.DEFAULT_SIZE,
																955,
																Short.MAX_VALUE)
														.addGroup(
																Alignment.TRAILING,
																gl_p_container
																		.createSequentialGroup()
																		.addComponent(
																				bt_apply)
																		.addPreferredGap(
																				ComponentPlacement.RELATED)
																		.addComponent(
																				bt_revert))
														.addGroup(
																gl_p_container
																		.createSequentialGroup()
																		.addComponent(
																				lb_name)
																		.addPreferredGap(
																				ComponentPlacement.RELATED)
																		.addComponent(
																				tf_name,
																				GroupLayout.DEFAULT_SIZE,
																				893,
																				Short.MAX_VALUE)))
										.addContainerGap()));
		gl_p_container
				.setVerticalGroup(gl_p_container
						.createParallelGroup(Alignment.LEADING)
						.addGroup(
								gl_p_container
										.createSequentialGroup()
										.addContainerGap()
										.addGroup(
												gl_p_container
														.createParallelGroup(
																Alignment.BASELINE)
														.addComponent(
																tf_name,
																GroupLayout.PREFERRED_SIZE,
																GroupLayout.DEFAULT_SIZE,
																GroupLayout.PREFERRED_SIZE)
														.addComponent(lb_name))
										.addPreferredGap(
												ComponentPlacement.RELATED)
										.addComponent(p_view,
												GroupLayout.PREFERRED_SIZE,
												466, GroupLayout.PREFERRED_SIZE)
										.addPreferredGap(
												ComponentPlacement.RELATED)
										.addGroup(
												gl_p_container
														.createParallelGroup(
																Alignment.BASELINE)
														.addComponent(bt_revert)
														.addComponent(bt_apply))
										.addContainerGap(
												GroupLayout.DEFAULT_SIZE,
												Short.MAX_VALUE)));
		p_container.setLayout(gl_p_container);

		// GroupLayout for p_header

		GroupLayout gl_p_header = new GroupLayout(p_header);
		gl_p_header.setHorizontalGroup(gl_p_header.createParallelGroup(
				Alignment.LEADING).addGroup(
				Alignment.TRAILING,
				gl_p_header
						.createSequentialGroup()
						.addContainerGap()
						.addComponent(ta_header, GroupLayout.DEFAULT_SIZE,
								1069, Short.MAX_VALUE).addGap(18)
						.addComponent(lb_icon).addGap(4)));
		gl_p_header
				.setVerticalGroup(gl_p_header
						.createParallelGroup(Alignment.LEADING)
						.addGroup(
								gl_p_header
										.createSequentialGroup()
										.addGap(6)
										.addGroup(
												gl_p_header
														.createParallelGroup(
																Alignment.BASELINE)
														.addComponent(
																ta_header,
																GroupLayout.DEFAULT_SIZE,
																44,
																Short.MAX_VALUE)
														.addComponent(lb_icon))
										.addContainerGap()));
		p_header.setLayout(gl_p_header);

		GroupLayout gl_p_commands = new GroupLayout(p_commands);
		gl_p_commands
				.setHorizontalGroup(gl_p_commands
						.createParallelGroup(Alignment.LEADING)
						.addGroup(
								gl_p_commands
										.createSequentialGroup()
										.addContainerGap()
										.addGroup(
												gl_p_commands
														.createParallelGroup(
																Alignment.LEADING)
														.addComponent(
																p_tree,
																GroupLayout.PREFERRED_SIZE,
																211,
																GroupLayout.PREFERRED_SIZE)
														.addComponent(
																p_buttons,
																GroupLayout.DEFAULT_SIZE,
																GroupLayout.DEFAULT_SIZE,
																Short.MAX_VALUE))
										.addContainerGap()));
		gl_p_commands.setVerticalGroup(gl_p_commands.createParallelGroup(
				Alignment.LEADING).addGroup(
				gl_p_commands
						.createSequentialGroup()
						.addContainerGap()
						.addComponent(p_buttons, GroupLayout.PREFERRED_SIZE,
								GroupLayout.DEFAULT_SIZE,
								GroupLayout.PREFERRED_SIZE)
						.addPreferredGap(ComponentPlacement.RELATED)
						.addComponent(p_tree, GroupLayout.DEFAULT_SIZE, 558,
								Short.MAX_VALUE).addContainerGap()));
		p_commands.setLayout(gl_p_commands);

		getContentPane().setLayout(groupLayout);
	}
}
