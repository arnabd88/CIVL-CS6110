package edu.udel.cis.vsl.civl.gui.common;

import java.awt.Component;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.File;
import java.util.ArrayList;

import javax.swing.JButton;
import javax.swing.JFileChooser;
import javax.swing.JFrame;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTable;
import javax.swing.filechooser.FileNameExtensionFilter;
import javax.swing.table.DefaultTableModel;

/**
 * This class opens up a simple dialog window from which the user can add or
 * remove paths from the SysIncludePath and UserIncludePath options.
 * 
 * @author StevenNoyes
 * 
 */
public class PathChooser extends JFrame {
	private JPanel p_container;
	private JScrollPane sp_fileTable;
	private JButton bt_browseFile;
	private JButton bt_cancel;
	private JButton bt_apply;
	private JTable tbl_fileTable;
	
	private ArrayList<String> filePaths;
	
	private String pathString;
	
	public String optName;
	
	public GUI_revamp parent;
	
	public PathChooser(String path, String optName, GUI_revamp parent) {
		super();
		this.optName = optName;
		this.parent = parent;
		filePaths = new ArrayList<String>();
		setPathString(path);
				
		this.setSize(500, 500);
		this.setLocationRelativeTo(this.getParent());

		initContainer();
		initActions();	

		this.setVisible(true);
	}
	
	/**
	 * Creates the container for the path include GUI
	 */
	public void initContainer() {
		// Init components
		p_container = new JPanel();
		sp_fileTable = new JScrollPane();
		bt_browseFile = new JButton("Browse");
		bt_apply = new JButton("Apply");
		bt_cancel = new JButton("Cancel");
		tbl_fileTable = new CIVLTable(new int[] { 2 }, "file", null);

		sp_fileTable.setViewportView(tbl_fileTable);
		tbl_fileTable.setModel(new DefaultTableModel(null, new String[] {
				"File Name", "File Path", "Delete" }));
		tbl_fileTable.setCellSelectionEnabled(true);
		tbl_fileTable.setRowHeight(30);
		
		final DefaultTableModel currFileModel = (DefaultTableModel) tbl_fileTable
				.getModel();
		
		ArrayList<String> arr = splitPathString();
		
		for(int i = 0; i < arr.size(); i++){
			currFileModel.addRow(new Object[] {
					arr.get(i), arr.get(i),
					"Delete" });
		}

		// Add main JPanel to this JFrame
		this.add(p_container);

		// Add components to p_container
		p_container.add(sp_fileTable);
		p_container.add(bt_browseFile);
		p_container.add(bt_apply);
		p_container.add(bt_cancel);		
	}
	
	private ArrayList<String> splitPathString(){
		StringBuffer sb = new StringBuffer();
		ArrayList<String> arrayOut = new ArrayList<String>();
		for (int i = 0; i < pathString.length(); i++) {
			  char c = pathString.charAt(i);
			  if(c == ':'){
				  arrayOut.add(sb.toString());
				  sb.delete(0, sb.length());
			  }
			  
			  else {
				  sb.append(c);
			  }
		}
		return arrayOut;
	}

	public void initActions() {
		ActionListener browseFile = new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				String examplesPath = "/Users/noyes/Documents/workspace/CIVL/examples";
				File start = new File(examplesPath);
				final JFileChooser chooser = new JFileChooser();
				//chooser.setCurrentDirectory(start);
				FileNameExtensionFilter filter = new FileNameExtensionFilter(
						"CIVL Files (.cvl)", "cvl");
				chooser.setFileFilter(filter);
				final DefaultTableModel currFileModel = (DefaultTableModel) tbl_fileTable
						.getModel();

				chooser.addActionListener(new ActionListener() {
					public void actionPerformed(ActionEvent e) {
						File selectedFile = chooser.getSelectedFile();
						// currConfig.setSelectedFile(selectedFile);
						currFileModel.addRow(new Object[] {
								selectedFile.getName(), selectedFile.getPath(),
								"Delete" });
						filePaths.add(selectedFile.getPath());
						// String[] filePaths = new String[files.length];
					}
				});
				chooser.showOpenDialog(null);
			}			
		};

		bt_browseFile.addActionListener(browseFile);
				
		ActionListener apply = new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				pathString = format();
				parent.save(pathString, optName);
				//rcdn.pathString_sys
				//System.out.println();
				//save();
			}
		};
		
		bt_apply.addActionListener(apply);
		
		/*
		//Have the JFrame save the value
		this.addWindowListener(
			new java.awt.event.WindowAdapter() {
		    @Override
		    	public void windowClosing(java.awt.event.WindowEvent windowEvent) {
		    		System.exit(0);
		    	}
			}
		);
		*/
	}

	/**
	 * Saves the values from the table in the form of an include path string
	 * 
	 * @return The string that represents the include path string
	 * 
	 */
	public String format() {
		String out = "";
		int size = filePaths.size();
		for(int i = 0; i < size; i++){
			if(i != size - 1)
				out += filePaths.get(i) + ":";
			
			else
				out += filePaths.get(i);
		}
		return out;
	}

	public String getPathString() {
		return pathString;
	}

	private void setPathString(String pathString) {
		this.pathString = pathString;
	}
}
