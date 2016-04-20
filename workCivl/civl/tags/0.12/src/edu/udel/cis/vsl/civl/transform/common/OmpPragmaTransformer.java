package edu.udel.cis.vsl.civl.transform.common;

import java.util.ArrayList;
import java.util.List;

import edu.udel.cis.vsl.abc.antlr2ast.IF.ASTBuilder;
import edu.udel.cis.vsl.abc.antlr2ast.IF.Antlr2AST;
import edu.udel.cis.vsl.abc.antlr2ast.IF.OmpBuilder;
import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode.NodeKind;
import edu.udel.cis.vsl.abc.ast.node.IF.PragmaNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpForNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.CompoundStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;
import edu.udel.cis.vsl.abc.err.IF.ABCRuntimeException;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;

public class OmpPragmaTransformer extends CIVLBaseTransformer {

	public final static String CODE = "_omp_";
	public final static String LONG_NAME = "Omp Parser";
	public final static String SHORT_DESCRIPTION = "parse omp pragmas into omp AST nodes";
	public final static String OMP = "omp";

	private OmpBuilder ompBuilder;

	public OmpPragmaTransformer(ASTFactory astFactory,
			List<String> inputVariables, ASTBuilder astBuilder, CIVLConfiguration config) {
		super(CODE, LONG_NAME, SHORT_DESCRIPTION, astFactory, inputVariables,
				astBuilder, config);
		this.ompBuilder = Antlr2AST.newOmpBuilder(astFactory, astBuilder);
	}

	@Override
	public AST transform(AST unit) throws SyntaxException {
		ASTNode root = unit.getRootNode();

		unit.release();
		this.processASTNode(root);
		return astFactory.newAST(root);
	}

	private void processASTNode(ASTNode ast) throws SyntaxException {
		int childNum = ast.numChildren();

		for (int i = childNum - 1; i >= 0; i--) {
			ASTNode child = ast.child(i);

			if (child == null)
				continue;
			if (child.nodeKind() == NodeKind.PRAGMA) {
				PragmaNode pragmaNode = (PragmaNode) child;

				if (pragmaNode.getPragmaIdentifier().name().equals(OMP)) {
					OmpNode ompNode = ompBuilder.getOmpNode(
							pragmaNode.getSource(), pragmaNode.getTokens());

					ast.removeChild(i);
					switch (ompNode.ompNodeKind()) {
					case EXECUTABLE:
						OmpStatementNode ompStatementNode = (OmpStatementNode) ompNode;

						if (ompStatementNode.isComplete()) {
							ast.setChild(i, ompNode);
						} else if (ompStatementNode instanceof OmpForNode) {
							OmpForNode ompForNode = (OmpForNode) ompStatementNode;
							int collapse = ompForNode.collapse();

							if (collapse == 1) {
								StatementNode forStatement = (StatementNode) ast
										.child(i + 1);

								forStatement.parent().removeChild(
										forStatement.childIndex());
								ompForNode.setStatementNode(forStatement);
							} else {
								List<BlockItemNode> forList = new ArrayList<>(
										collapse);
								CompoundStatementNode compoundStatement;
								Source source = ast.child(i + 1).getSource();

								for (int k = 1; k <= collapse; k++) {
									StatementNode forStatement = (StatementNode) ast
											.child(i + k);

									forStatement.parent().removeChild(
											forStatement.childIndex());
									forList.add(forStatement);
								}
								compoundStatement = nodeFactory
										.newCompoundStatementNode(source,
												forList);
								ompForNode.setStatementNode(compoundStatement);
							}
							ast.setChild(i, ompForNode);
						} else {
							StatementNode statementNode = (StatementNode) ast
									.child(i + 1);

							statementNode.parent().removeChild(
									statementNode.childIndex());
							ompStatementNode.setStatementNode(statementNode);
							ast.setChild(i, ompStatementNode);
						}
						break;
					case DECLARATIVE:
						ast.setChild(i, ompNode);
						break;
					default:
						throw new ABCRuntimeException("Unreachable");
					}
				} else {
					this.processASTNode(child);
				}
			} else {
				this.processASTNode(child);
			}
		}

	}
}
