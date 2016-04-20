package edu.udel.cis.vsl.civl.gui.common;

import java.util.EventListener;

interface SaveTableListener extends EventListener{
	public void SaveTableTriggered(SaveTableEvent evt);
}
