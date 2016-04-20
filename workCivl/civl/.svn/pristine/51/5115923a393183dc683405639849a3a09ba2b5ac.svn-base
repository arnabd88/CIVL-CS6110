package edu.udel.cis.vsl.civl.gui.common;

/**
 * 
 * This class is responsible for launching the entire CIVL GUI. It takes signals
 * from the various frames that compose this GUI. These signals indicate whether
 * a frame should be visible or not.
 * 
 * @author noyes
 * 
 */

public class Launch {
	/**
	 * This is the start frame which is merely the menu from which a user can
	 * load or create their run configuration
	 */
	private static StartFrame stf;

	/**
	 * The option frame is the frame from which the user chooses a file, command
	 * and all additional options they would like to implement.
	 */
	private static OptionFrame opf;

	/**
	 * The input frame is the frame from which the user can specify input for
	 * their run configuration if they are doing run or verify.
	 */
	private static InputFrame inf;

	public Launch() {
		stf = new StartFrame(true);
		inf = new InputFrame(false);
		opf = new OptionFrame(false);
	}

	public void start() {
		while (true) {
			if (stf.gotoOptions) {
				stf.setVisible(false);
				opf.setVisible(true);
				stf.gotoOptions = false;
			}

			if (opf.gotoInputs) {
				opf.setVisible(false);
				inf.setVisible(true);
				opf.gotoInputs = false;
			}
			if (opf.cancelled) {
				stf.setVisible(true);
				inf.setVisible(false);
				opf.setVisible(false);
				opf.cancelled = false;
			}
			if (opf.finalized) {
				stf.setVisible(true);
				inf.setVisible(false);
				opf.setVisible(false);
				opf.finalized = false;
			}

			if (inf.done) {
				inf.setVisible(false);
				stf.setVisible(true);
				inf.done = false;
			}
			if (inf.cancelled) {
				opf.setVisible(true);
				inf.setVisible(false);
				inf.cancelled = false;
			}

		}
	}

}
