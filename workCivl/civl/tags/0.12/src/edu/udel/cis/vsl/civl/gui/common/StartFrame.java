package edu.udel.cis.vsl.civl.gui.common;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.File;

import javax.swing.JFileChooser;
import javax.swing.JFrame;
import javax.swing.JMenu;
import javax.swing.JMenuBar;
import javax.swing.JMenuItem;

/**
 * StartFrame is simply the first thing the user sees when they launch the CIVL
 * GUI. It only contains a JMenu from which a user can either load or create a
 * new run configuration.
 * 
 * @author noyes
 * 
 */
@SuppressWarnings("serial")
public class StartFrame extends JFrame {
	/**
	 * This boolean is a flag that tells the Launch class to switch frames from the <code>StartFrame</code> to the <code>OptionFrame</code>.
	 */
	public boolean gotoOptions;
	
	//TODO: Make it so there is no JFrame visible, just the menu should be.
	
	public StartFrame(boolean visible) {
		gotoOptions = false;
		System.setProperty("apple.laf.useScreenMenuBar", "true");
		//System.setProperty("com.apple.mrj.application.apple.menu.about.name", "CIVL"); TODO doesn't display CIVL as the name!!!
		setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
		setVisible(true);
		setJMenuBar(initMenus());
		setSize(50, 50);
	}
	
	/**
	 * This function initializes the main JMenu used to create/load a run configuration. 
	 * 
	 * @return
	 * 		This function returns the initialized JMenuBar so that it can be added to the JFrame
	 */
	public JMenuBar initMenus() {
		JMenu menu = new JMenu("File");
		JMenuBar menuBar = new JMenuBar();
		JMenuItem newRunConfigMenu = new JMenuItem("New Run Configuration");
		JMenuItem openRunConfigMenu = new JMenuItem("Open Run Configuration");
		openRunConfigMenu.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				String examplesPath = "/Users/noyes/Documents/workspace/TestGUI/RunConfigurations";
				File start = new File(examplesPath);
				final JFileChooser chooser = new JFileChooser();
				chooser.setCurrentDirectory(start);
				// parser for open file and adding to source code window
				chooser.addActionListener(new ActionListener() {
					public void actionPerformed(ActionEvent e) {
						@SuppressWarnings("unused")
						File selected = chooser.getSelectedFile();
					}
				});
				chooser.showOpenDialog(null);
			}
		});

		newRunConfigMenu.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				gotoOptions = true;
			}

		});

		menu.add(newRunConfigMenu);
		menu.add(openRunConfigMenu);
		menuBar.add(menu);

		return menuBar;
	}

	public static void main(String[] args) {
		@SuppressWarnings("unused")
		StartFrame start = new StartFrame(true);

	}

}
