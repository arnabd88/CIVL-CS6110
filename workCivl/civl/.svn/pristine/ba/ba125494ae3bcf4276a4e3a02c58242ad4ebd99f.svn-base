package edu.udel.cis.vsl.civl.gui.common;
import javax.swing.JFrame;
import javax.swing.JTable;
import javax.swing.table.DefaultTableModel;

import java.awt.Font;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.JScrollPane;
import javax.swing.JLabel;
import javax.swing.JButton;

/**
 * 
 * The InputFrame is an extension of JFrame that is used to specify the inputs
 * the user would like for their run configuration.
 * 
 * @author noyes
 * 
 */
@SuppressWarnings("serial")
public class InputFrame extends JFrame {
	private JTable table_1;
	public boolean done;
	public boolean cancelled;
	private JScrollPane scrollPane;

	public InputFrame(boolean visible) {
		done = false;
		cancelled = false;
		getContentPane().setLayout(null);
		setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
		setVisible(visible);
		initTables();
		initButtons();
		initLabels();
		setSize(1098, 711);
	}
	
	/**
	 * This function initializes all of the JTables in the frame.
	 */
	public void initTables() {
		scrollPane = new JScrollPane();
		scrollPane.setBounds(50, 50, 985, 52);
		getContentPane().add(scrollPane);

		table_1 = new JTable();
		scrollPane.setViewportView(table_1);
		table_1.setCellSelectionEnabled(true);
		table_1.setModel(new DefaultTableModel(new Object[][] { { "var", "ty",
				"val" }, }, new String[] { "Variable", "Type", "Value" }));
	}
	
	/**
	 * This function initializes all of the JButtons in the frame.
	 */
	public void initButtons() {
		JButton btnFinalize = new JButton("Finalize");
		btnFinalize.setBounds(847, 654, 117, 29);
		btnFinalize.addActionListener(new ActionListener() {
			@Override
			public void actionPerformed(ActionEvent e) {
				done = true;
			}
		});
		getContentPane().add(btnFinalize);

		JButton btnCancel = new JButton("Cancel");
		btnCancel.setBounds(966, 654, 117, 29);
		btnCancel.addActionListener(new ActionListener() {
			@Override
			public void actionPerformed(ActionEvent e) {
				cancelled = true;
				reset();
			}
		});
		getContentPane().add(btnCancel);
	}
	
	/**
	 * This function initializes all of the JLabels in the frame.
	 */
	public void initLabels() {
		JLabel lblSetInputs = new JLabel("Set Inputs");
		lblSetInputs.setFont(new Font("Lucida Grande", Font.PLAIN, 19));
		lblSetInputs.setBounds(10, 6, 190, 29);
		getContentPane().add(lblSetInputs);
	}
	
	/**
	 * This function clears the input table when the user hits cancel.
	 */
	public void reset() {
		getContentPane().remove(table_1);
		getContentPane().remove(scrollPane);
		scrollPane = new JScrollPane();
		scrollPane.setBounds(50, 50, 985, 52);
		initTables();

	}

	public static void main(String[] args) {}
}
