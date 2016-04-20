package edu.udel.cis.vsl.abc.program.IF;

import edu.udel.cis.vsl.abc.analysis.IF.Analyzer;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.program.common.CommonProgramFactory;

public class Programs {

	public static ProgramFactory newProgramFactory(ASTFactory factory,
			Analyzer standardAnalyzer) {
		return new CommonProgramFactory(factory, standardAnalyzer);
	}

}
