package edu.udel.cis.vsl.abc.front.c.preproc;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;

import org.antlr.runtime.ANTLRStringStream;

/**
 * An ANTLR stream which reads from a file and removes any two consecutive
 * characters that are backslash followed by newline. This is part of the C
 * translation process.
 * 
 * @author siegel
 */
public class FilteredANTLRFileStream extends ANTLRStringStream {

	protected File file;

	public FilteredANTLRFileStream(File file, String encoding)
			throws IOException {
		this.file = file;
		load(file, encoding);
	}

	public FilteredANTLRFileStream(File file) throws IOException {
		this(file, null);
	}

	public FilteredANTLRFileStream(String string) throws IOException {
		this.file = null;
		load(string);
	}

	private void load(InputStream fis, int size, String encoding)
			throws IOException {
		InputStreamReader isr;

		if (encoding != null) {
			isr = new InputStreamReader(fis, encoding);
		} else {
			isr = new InputStreamReader(fis);
		}
		try {
			data = new char[size];
			int numUnfilteredChars = isr.read(data);
			int numFilteredChars = 0;

			for (int i = 0; i < numUnfilteredChars; i++) {
				char c = data[i];

				if (c == '\\' && i < numUnfilteredChars - 1
						&& data[i + 1] == '\n') {
					i++;
				} else {
					data[numFilteredChars] = c;
					numFilteredChars++;
				}
			}
			// I believe the following truncation of array data is
			// unnecessary. It suffices to set n.
			// super.data = Arrays.copyOf(data, numFilteredChars);
			super.n = numFilteredChars;
		} finally {
			isr.close();
		}
	}

	private void load(File file, String encoding) throws IOException {
		int size = (int) file.length();
		FileInputStream fis = new FileInputStream(file);

		load(fis, size, encoding);
	}

	private void load(String string) throws IOException {
		load(new ByteArrayInputStream(string.getBytes()), string.length(), null);
	}

	@Override
	public String getSourceName() {
		return file.getName();
	}
}
