package edu.udel.cis.vsl.civl.gui.common;

import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Component;
import java.awt.Container;
import java.awt.FlowLayout;
import java.awt.Font;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.File;
import java.io.IOException;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.Map;

import javax.swing.AbstractAction;
import javax.swing.Action;
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
import javax.swing.border.LineBorder;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;
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
	private CIVL_Command currCommand;

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
	
	private static String serializePath;

	protected RunConfigDataNode cachedConfig;

	public GUI_revamp() {
		setVisible(true);
		setDefaultCloseOperation(EXIT_ON_CLOSE);
		setSize(1200, 700);
		componentMap = new HashMap<String, Component>();
		newConfigsNum = 0;
		
		String currDirect = null;
		try {
			currDirect = new File(".").getCanonicalPath();
		} catch (IOException e) {
			e.printStackTrace();
		}
		setSerializePath(currDirect + "/doc/RunConfigs");

		initCIVL_Commands();
		loadSavedConfigsMap();
		initCommandsPanel();
		initContainer();
		initHeader();
		initExecute();
		createComponentMap(this);
		initLayouts();
		initListeners(this);

	}
	
	public void setSerializePath(String path){
		serializePath = path;
	}

	public void loadSavedConfigsMap() {
		// deserialize()
		//RunConfigDataNode config = null;
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
			} else {
				//if(fileEntry.exstension != ".ser"){
				RunConfigDataNode temp = new RunConfigDataNode(new CIVL_Command("", "", null, false));
				temp.setName(fileEntry.getName());
				temp.setSerializeDestination(serializePath);
				savedConfigs.put(fileEntry.getName(), temp.deserialize());
				//}
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
			return (Component) componentMap.get(name);
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
			// TODO: change this to a thrown exception
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
	 * Sets the options for the option table of the current run configuration.
	 */
	public void setOptions() {
		CIVLTable tbl_optionTable = (CIVLTable) getComponentByName("tbl_optionTable");
		DefaultTableModel optionModel = (DefaultTableModel) tbl_optionTable
				.getModel();
		if (optionModel.getRowCount() != 0) {
			optionModel.setRowCount(0);
			tbl_optionTable.clearSelection();
		}
		Option[] options = currCommand.getAllowedOptions();
		for (int i = 0; i < currConfig.getValues().length; i++) {
			optionModel.addRow(new Object[] { options[i],
					currConfig.getValues()[i], "Default" });
			new ButtonColumn(tbl_optionTable, defaultize, 2);
		}
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

			currCommand = currConfig.getCommand();

			if (currCommand.getName() == "parse") {
				tp_commandView.addTab("Choose File", p_chooseFile);
				p_view.add(tp_commandView);
				p_view.validate();

			} else if (currCommand.getName() == "preprocess") {
				tp_commandView.addTab("Choose File", p_chooseFile);
				p_view.add(tp_commandView);
				p_view.validate();

			} else if (currCommand.getName() == "replay") {
				tp_commandView.addTab("Choose File", p_chooseFile);
				p_view.add(tp_commandView);
				p_view.validate();

			} else if (currCommand.getName() == "run") {
				tp_commandView.addTab("Choose File", p_chooseFile);
				tp_commandView.addTab("Options", p_options);
				tp_commandView.addTab("Inputs", p_inputs);
				setOptions();
				p_view.add(tp_commandView);
				p_view.validate();

			} else if (currCommand.getName() == "verify") {
				tp_commandView.addTab("Choose File", p_chooseFile);
				tp_commandView.addTab("Options", p_options);
				tp_commandView.addTab("Inputs", p_inputs);
				setOptions();
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
	 * Initializes all of the {@link CIVL_Command} that are currently supported.
	 */
	public void initCIVL_Commands() {
		commands = new CIVL_Command[5];
		Option[] options = CIVLConstants.getAllOptions();

		CIVL_Command parse = new CIVL_Command("parse",
				"show result of preprocessing and parsing filename",
				new Option[] {}, false);
		CIVL_Command preprocess = new CIVL_Command("preprocess",
				"show result of preprocessing filename", new Option[] {}, false);
		CIVL_Command replay = new CIVL_Command("replay",
				"replay trace for program filename", new Option[] {}, false);
		CIVL_Command run = new CIVL_Command("run", "run program filename",
				options, true);
		CIVL_Command verify = new CIVL_Command("verify",
				"verify program filename", options, true);

		commands[0] = parse;
		commands[1] = preprocess;
		commands[2] = replay;
		commands[3] = run;
		commands[4] = verify;
	}

	/**
	 * Creates the command {@link JPanel}.
	 */
	public void initCommandsPanel() {
		JPanel p_commands = new JPanel();
		JButton bt_new = new JButton("N");
		JButton bt_duplicate = new JButton("D");
		JButton bt_deleteConfig = new JButton("X");
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
	// TODO: make tf_name actually change the name of the config
	// TODO: have a unsaved changes pop up window like eclipse run configs
	public void initContainer() {
		JPanel p_container = new JPanel();
		JPanel p_view = new JPanel();
		JPanel p_info = new JPanel();
		JPanel p_chooseFile = new JPanel();
		JPanel p_options = new JPanel();
		JPanel p_inputs = new JPanel();
		JScrollPane sp_optionTable = new JScrollPane();
		JScrollPane sp_inputTable = new JScrollPane();
		JTabbedPane tp_commandView = new JTabbedPane();
		JButton bt_revert = new JButton("Revert");
		JButton bt_apply = new JButton("Apply");
		JButton bt_browseFile = new JButton("Browse...");
		JLabel lb_name = new JLabel("Name: ");
		JLabel lb_chooseFile = new JLabel("Chosen File: ");
		JLabel lb_new = new JLabel(
				"New - Press the new button to create a new run configuration of the selected type.");
		JLabel lb_duplicate = new JLabel(
				"Duplicate - Press the 'duplicate' button to duplicate the currently selected run configuration.");
		JLabel lb_delete = new JLabel(
				"Delete - Press the 'delete' button to delete the currently selected run configuration.");
		JTextField tf_name = new JTextField();
		JTextField tf_chooseFile = new JTextField();
		JTable tbl_optionTable = new CIVLTable(new int[] { 1, 2 }, "option");
		JTable tbl_inputTable = new CIVLTable(new int[] { 2 }, "input");

		tf_chooseFile.setColumns(58);
		tf_name.setColumns(10);

		p_options.setLayout(new BorderLayout(0, 0));
		p_inputs.setLayout(new BorderLayout(0, 0));

		p_container.setName("p_container");
		p_view.setName("p_view");
		p_info.setName("p_info");
		p_chooseFile.setName("p_chooseFile");
		p_options.setName("p_options");
		p_inputs.setName("p_inputs");
		sp_optionTable.setName("sp_optionTable");
		sp_inputTable.setName("sp_inputTable");
		tp_commandView.setName("tp_commandView");
		bt_revert.setName("bt_revert");
		bt_apply.setName("bt_apply");
		bt_browseFile.setName("bt_browseFile");
		tf_name.setName("tf_name");
		tf_chooseFile.setName("tf_chooseFile");
		lb_name.setName("lb_name");
		tbl_optionTable.setName("tbl_optionTable");
		tbl_inputTable.setName("tbl_inputTable");

		lb_new.setBounds(6, 6, 554, 16);
		lb_duplicate.setBounds(6, 39, 589, 16);
		lb_delete.setBounds(6, 72, 589, 16);

		sp_optionTable.setViewportView(tbl_optionTable);
		sp_inputTable.setViewportView(tbl_inputTable);
		tbl_optionTable.setModel(new DefaultTableModel(null, new String[] {
				"Option", "Value", "Default" }));
		tbl_inputTable.setModel(new DefaultTableModel(null, new String[] {
				"Variable", "Type", "Value" }));
		tbl_optionTable.setCellSelectionEnabled(true);
		tbl_inputTable.setCellSelectionEnabled(true);
		tbl_optionTable.setRowHeight(30);
		tbl_inputTable.setRowHeight(30);

		p_container.add(p_view);
		p_container.add(bt_revert);
		p_container.add(bt_apply);
		p_container.add(tf_name);
		p_container.add(lb_name);

		p_info.add(lb_new);
		p_info.add(lb_duplicate);
		p_info.add(lb_delete);

		p_chooseFile.add(lb_chooseFile);
		p_chooseFile.add(tf_chooseFile);
		p_chooseFile.add(bt_browseFile);

		p_options.add(sp_optionTable);
		p_inputs.add(sp_inputTable);

		addToMap(p_info);
		addToMap(tp_commandView);
		addToMap(p_chooseFile);
		addToMap(p_options);
		addToMap(p_inputs);
		addToMap(bt_browseFile);
		addToMap(tf_chooseFile);
		addToMap(sp_optionTable);
		addToMap(sp_inputTable);
		addToMap(tbl_optionTable);
		addToMap(tbl_inputTable);

		add(p_container);

		revalidate();
		repaint();
	}

	/**
	 * Creates the execute {@link JPanel}.
	 */
	public void initExecute() {
		JPanel p_execute = new JPanel();
		JButton bt_cancel = new JButton("Cancel");
		JButton bt_run = new JButton("Run");

		p_execute.setName("p_execute");
		bt_cancel.setName("bt_cancel");
		bt_run.setName("bt_run");

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
	 * 
	 * @return The node that will be the root of jt_commands
	 */
	public DefaultMutableTreeNode initNodes() {
		DefaultMutableTreeNode top = new DefaultMutableTreeNode("commands");
		DefaultMutableTreeNode parseNode = new DefaultMutableTreeNode("parse");
		DefaultMutableTreeNode preprocessNode = new DefaultMutableTreeNode(
				"preprocess");
		DefaultMutableTreeNode replayNode = new DefaultMutableTreeNode("replay");
		DefaultMutableTreeNode runNode = new DefaultMutableTreeNode("run");
		DefaultMutableTreeNode verifyNode = new DefaultMutableTreeNode("verify");

		top.add(parseNode);
		top.add(preprocessNode);
		top.add(replayNode);
		top.add(runNode);
		top.add(verifyNode);

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
		final JButton bt_run = (JButton) getComponentByName("bt_run");
		final JButton bt_apply = (JButton) getComponentByName("bt_apply");
		final JButton bt_browseFile = (JButton) getComponentByName("bt_browseFile");
		final JTextField tf_name = (JTextField) getComponentByName("tf_name");
		final JTextField tf_chooseFile = (JTextField) getComponentByName("tf_chooseFile");
		final CIVLTable tbl_optionTable = (CIVLTable) getComponentByName("tbl_optionTable");

		jt_commands.setExpandsSelectedPaths(true);
		jt_commands.addTreeSelectionListener(new TreeSelectionListener() {
			public void valueChanged(TreeSelectionEvent e) {
				String headerText = "  Create, manage and run configurations\n";
				TreePath selected = jt_commands.getSelectionPath();
				DefaultMutableTreeNode node = (DefaultMutableTreeNode) jt_commands
						.getLastSelectedPathComponent();
				if (selected.getPathCount() == 2) {
					if (currConfig != null && !currConfig.isBrandNew()) {
						if (currConfig.isChanged()) {
							boolean saveConfig;
							int response = JOptionPane
									.showConfirmDialog(
											gui,
											"There are unsaved changes in the current "
													+ "Run Configuration, do you want to save changes?",
											"Save Changes?",
											JOptionPane.YES_NO_OPTION);

							if (response == 1)
								saveConfig = false;

							else {
								saveConfig = true;
							}

							currConfig.saveChanges(saveConfig);
						}
					}
					cachedConfig = currConfig;
					currConfig = null;
					drawView();
					tf_name.setText("");
					currCommand = getCommand(node.toString());
					headerText += "  " + currCommand.getName() + ": "
							+ currCommand.getDescription();
					ta_header.setText(headerText);
				}

				else if (selected.getPathCount() == 3) {
					if (currConfig != null && !currConfig.isBrandNew()) {
						if (currConfig.isChanged()) {
							boolean saveConfig;
							int response = JOptionPane
									.showConfirmDialog(
											gui,
											"There are unsaved changes in the current "
													+ "Run Configuration, do you want to save changes?",
											"Save Changes?",
											JOptionPane.YES_NO_OPTION);

							if (response == 1)
								saveConfig = false;

							else {
								saveConfig = true;
							}

							currConfig.saveChanges(saveConfig);
						}
					}
					cachedConfig = currConfig;
					currConfig = (RunConfigDataNode) node;
					currConfig.setBrandNew(false);
					tf_name.setText(currConfig.getName());
					drawView();
				} else {
					ta_header.setText(headerText + "  Choose a Command");
					tf_name.setText("");
				}

				revalidate();
				repaint();
			}
		});

		ActionListener browseFile = new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				// TODO: fix this so it points to the user's home dir
				String examplesPath = "/Users/noyes/Documents/workspace/CIVL/examples";
				File start = new File(examplesPath);
				final JFileChooser chooser = new JFileChooser();
				chooser.setCurrentDirectory(start);
				FileNameExtensionFilter filter = new FileNameExtensionFilter(
						"CIVL Files (.cvl)", "cvl");
				chooser.setFileFilter(filter);
				chooser.addActionListener(new ActionListener() {
					public void actionPerformed(ActionEvent e) {
						File selectedFile = chooser.getSelectedFile();
						currConfig.setSelectedFile(selectedFile);
						tf_chooseFile.setText(selectedFile.getName());
					}
				});
				chooser.showOpenDialog(null);
			}
		};

		bt_browseFile.addActionListener(browseFile);

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

		ActionListener apply = new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				currConfig.saveChanges(true);
				currConfig.setUserObject(currConfig.getName());
				revalidate();
				repaint();
				currConfig.serialize();
			}
		};

		bt_apply.addActionListener(apply);

		ActionListener run = new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				currConfig.deserialize();
			}
		};

		bt_run.addActionListener(run);

		ActionListener newConfig = new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				Option[] options = CIVLConstants.getAllOptions();
				DefaultTreeModel treeModel = (DefaultTreeModel) jt_commands
						.getModel();
				Object config = savedConfigs.get(tf_name.getText());
				boolean dontCreate = false;
				DefaultMutableTreeNode node = (DefaultMutableTreeNode) jt_commands
						.getLastSelectedPathComponent();
				CIVL_Command selectedCom = getCommand(node.toString());

				if (config != null) {
					dontCreate = true;
				}

				if (!dontCreate) {
					TreePath selected = jt_commands.getSelectionPath();

					DefaultMutableTreeNode selectedNode = (DefaultMutableTreeNode) jt_commands
							.getLastSelectedPathComponent();

					DefaultMutableTreeNode newChild = new RunConfigDataNode(
							selectedCom);
					String newName = tf_name.getText();
					if (tf_name.getText().equals(null)
							|| tf_name.getText().equals("")) {
						newName = "New Configuration(" + newConfigsNum + ")";
						if (selected.getPathCount() == 2) {
							newConfigsNum++;
						}
					}

					newChild.setUserObject(newName);
					currConfig = (RunConfigDataNode) newChild;
					currConfig.setName(newName);
					((RunConfigDataNode) currConfig)
							.setSerializeDestination(serializePath);

					for (int i = 0; i < currConfig.getValues().length; i++) {
						currConfig.getValues()[i] = options[i].defaultValue();
					}

					savedConfigs.put(currConfig.getName(), currConfig);

					if (selected.getPathCount() != 1)
						tf_name.setText(newName);

					if (selected.getPathCount() == 2) {
						((DefaultTreeModel) jt_commands.getModel())
								.insertNodeInto(currConfig, selectedNode,
										selectedNode.getChildCount());

						TreePath currPath = getTreePath(
								(DefaultMutableTreeNode) treeModel.getRoot(),
								currConfig.toString());
						jt_commands.setSelectionPath(currPath);

					}
				}
				dontCreate = false;

			}
		};
		bt_new.addActionListener(newConfig);

		// TODO: make it so when the user goes from tf_name
		/*
		 * tf_name.addFocusListener(new FocusListener() {
		 * 
		 * @Override public void focusGained(FocusEvent e) {
		 * 
		 * }
		 * 
		 * @Override public void focusLost(FocusEvent e) { if (currConfig !=
		 * null) { currConfig.setTemp_name(tf_name.getText()); //
		 * currConfig.setUserObject(currConfig.getName()); } }
		 * 
		 * });
		 */

		tf_name.getDocument().addDocumentListener(new DocumentListener() {

			@Override
			public void insertUpdate(DocumentEvent e) {
				currConfig.setTemp_name(tf_name.getText());
			}

			@Override
			public void removeUpdate(DocumentEvent e) {
				if (currConfig == null)
					cachedConfig.setTemp_name(tf_name.getText());
				else
					currConfig.setTemp_name(tf_name.getText());
			}

			@Override
			public void changedUpdate(DocumentEvent e) {
				currConfig.setTemp_name(tf_name.getText());
			}
		});

		tbl_optionTable.addSaveTableListener(new SaveTableListener() {
			DefaultTableModel optionModel = (DefaultTableModel) tbl_optionTable
					.getModel();

			@Override
			public void SaveTableTriggered(SaveTableEvent evt) {
				System.out.println("save table event caught");
				Object[] temp_values = new Object[optionModel.getRowCount()];
				for (int i = 0; i < optionModel.getRowCount(); i++) {
					temp_values[i] = optionModel.getValueAt(i, 1);
				}
				currConfig.setTemp_values(temp_values);
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

		p_header.setBorder(new LineBorder(new Color(0, 0, 0)));
		p_container.setBorder(new LineBorder(new Color(0, 0, 0)));
		p_commands.setBorder(new LineBorder(new Color(0, 0, 0)));
		p_execute.setBorder(new LineBorder(new Color(0, 0, 0)));
		p_view.setBorder(new LineBorder(new Color(0, 0, 0)));
		p_tree.setBorder(new LineBorder(new Color(0, 0, 0)));
		p_buttons.setBorder(new LineBorder(new Color(0, 0, 0)));

		p_buttons.setLayout(new FlowLayout(FlowLayout.LEFT, 1, 1));
		p_chooseFile.setLayout(new FlowLayout(FlowLayout.LEFT, 6, 1));
		p_view.setLayout(new BorderLayout(0, 0));
		p_info.setLayout(null);

		// GroupLayout for main JFrame
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
