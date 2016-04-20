package edu.udel.cis.vsl.abc.program.common;

import java.io.PrintStream;
import java.util.LinkedList;
import java.util.List;

import edu.udel.cis.vsl.abc.analysis.IF.Analyzer;
import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode.NodeKind;
import edu.udel.cis.vsl.abc.program.IF.Program;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.abc.token.IF.TokenFactory;
import edu.udel.cis.vsl.abc.transform.IF.Transform;
import edu.udel.cis.vsl.abc.transform.IF.Transformer;

public class CommonProgram implements Program {

	private Analyzer standardAnalyzer;

	private AST ast;

	public CommonProgram(Analyzer standardAnalyzer, AST ast)
			throws SyntaxException {
		this.standardAnalyzer = standardAnalyzer;
		this.ast = ast;
		standardAnalyzer.clear(ast);
		standardAnalyzer.analyze(ast);
	}

	@Override
	public AST getAST() {
		return ast;
	}

	@Override
	public void print(PrintStream out) {
		ast.print(out);
	}

	@Override
	public void prettyPrint(PrintStream out) {
		ast.prettyPrint(out, false);
	}

	@Override
	public void printSymbolTable(PrintStream out) {
		ast.getRootNode().getScope().print(out);
	}

	@Override
	public TokenFactory getTokenFactory() {
		return ast.getASTFactory().getTokenFactory();
	}

	@Override
	public void apply(Transformer transformer) throws SyntaxException {
		ast = transformer.transform(ast);
		standardAnalyzer.clear(ast);

		// debugging:
		// ast.prettyPrint(System.out, true);

		standardAnalyzer.analyze(ast);
	}

	@Override
	public void applyTransformer(String code) throws SyntaxException {
		Transformer transformer = Transform.newTransformer(code,
				ast.getASTFactory());

		apply(transformer);
	}

	@Override
	public void apply(Iterable<Transformer> transformers)
			throws SyntaxException {
		for (Transformer transformer : transformers) {
			ast = transformer.transform(ast);
			standardAnalyzer.clear(ast);
			standardAnalyzer.analyze(ast);
		}
	}

	@Override
	public void applyTransformers(Iterable<String> codes)
			throws SyntaxException {
		List<Transformer> transformers = new LinkedList<>();
		ASTFactory astFactory = ast.getASTFactory();

		for (String code : codes)
			transformers.add(Transform.newTransformer(code, astFactory));
		apply(transformers);
	}

	@Override
	public boolean hasOmpPragma() {
		return this.hasOmpPragmaInASTNode(ast.getRootNode());
	}

	private boolean hasOmpPragmaInASTNode(ASTNode node) {
		if (node.nodeKind() == NodeKind.OMP_NODE) {
//			PragmaNode pragmaNode = (PragmaNode) node;
//			if (pragmaNode.getPragmaIdentifier().name().equals("omp"))
				return true;
		} else {
			for (ASTNode child : node.children()) {
				if (child != null)
					if (this.hasOmpPragmaInASTNode(child))
						return true;
			}
		}
		return false;
	}
}
