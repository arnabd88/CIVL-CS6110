package edu.udel.cis.vsl.abc.ast.common;

import java.io.PrintStream;
import java.util.Stack;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode.NodeKind;
import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.PairNode;
import edu.udel.cis.vsl.abc.ast.node.IF.PragmaNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.StaticAssertionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.AssignsOrReadsNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.AssumesNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.BehaviorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.CallEventNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.CompositeEventNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.CompositeEventNode.EventOperator;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.ContractNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.ContractNode.ContractKind;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.DependsEventNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.DependsEventNode.DependsEventNodeKind;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.DependsNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.EnsuresNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.GuardsNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.InvariantNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.MPICollectiveBlockNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.MPIContractExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.MemoryEventNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.RequiresNode;
import edu.udel.cis.vsl.abc.ast.node.IF.compound.ArrayDesignatorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.compound.CompoundInitializerNode;
import edu.udel.cis.vsl.abc.ast.node.IF.compound.DesignationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.compound.DesignatorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.compound.FieldDesignatorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.AbstractFunctionDefinitionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.EnumeratorDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FieldDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDefinitionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.InitializerNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.TypedefDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.AlignOfNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ArrowNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.CallsNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.CastNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.CompoundLiteralNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ConstantNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ContractVerifyNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.DerivativeExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.DotNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode.ExpressionKind;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FunctionCallNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IntegerConstantNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode.Operator;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.QuantifiedExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.RegularRangeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.RemoteExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ScopeOfNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.SizeableNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.SizeofNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.SpawnNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.StatementExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.label.LabelNode;
import edu.udel.cis.vsl.abc.ast.node.IF.label.OrdinaryLabelNode;
import edu.udel.cis.vsl.abc.ast.node.IF.label.SwitchLabelNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpDeclarativeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpDeclarativeNode.OmpDeclarativeNodeKind;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpExecutableNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpExecutableNode.OmpExecutableKind;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpForNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpForNode.OmpScheduleKind;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpFunctionReductionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpNode.OmpNodeKind;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpParallelNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpReductionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpSymbolReductionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpSyncNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpSyncNode.OmpSyncNodeKind;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpWorksharingNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpWorksharingNode.OmpWorksharingNodeKind;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.AtomicNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode.BlockItemKind;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ChooseStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.CivlForNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.CompoundStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.DeclarationListNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ExpressionStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ForLoopInitializerNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ForLoopNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.GotoNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.IfNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.JumpNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.JumpNode.JumpKind;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.LabeledStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.LoopNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.LoopNode.LoopKind;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ReturnNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode.StatementKind;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.SwitchNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.WhenNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.ArrayTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.BasicTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.DomainTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.EnumerationTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.FunctionTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.PointerTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.StructureOrUnionTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode.TypeNodeKind;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypedefNameNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeofNode;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType.BasicTypeKind;
import edu.udel.cis.vsl.abc.err.IF.ABCRuntimeException;
import edu.udel.cis.vsl.abc.err.IF.ABCUnsupportedException;
import edu.udel.cis.vsl.abc.token.IF.CivlcToken;
import edu.udel.cis.vsl.abc.util.IF.Pair;

/**
 * This class implements the pretty printing of AST nodes. The purpose is to
 * print an AST in the original programming language and the output is expected
 * to be compiled into an equivalent AST.
 * 
 * @author Manchun Zheng
 * 
 */
public class ASTPrettyPrinter {

	/* ************************ Private Static Fields ********************** */

	private static String indention = "  ";

	private static int headerLength = 60;

	/* ******************* Package-private Static Methods ****************** */

	// FIX ME : I am public now

	@SuppressWarnings("unchecked")
	public static void prettyPrint(ASTNode node, PrintStream out) {
		NodeKind kind = node.nodeKind();

		switch (kind) {
		case DECLARATION_LIST:
			out.print(declarationList2Pretty((DeclarationListNode) node));
			break;
		case ENUMERATOR_DECLARATION:
			out.print(enumeratorDeclaration2Pretty((EnumeratorDeclarationNode) node));
			break;
		case EXPRESSION:
			out.print(expression2Pretty((ExpressionNode) node));
			break;
		case FIELD_DECLARATION:
			out.print(fieldDeclaration2Pretty("", (FieldDeclarationNode) node));
			break;
		case FUNCTION_DECLARATION:
			pPrintFunctionDeclaration(out, "", (FunctionDeclarationNode) node);
			break;
		case FUNCTION_DEFINITION:
			pPrintFunctionDeclaration(out, "", (FunctionDeclarationNode) node);
			break;
		case IDENTIFIER:
			out.print(((IdentifierNode) node).name());
			break;
		case OMP_NODE:
			pPrintOmpNode(out, "", (OmpNode) node);
			break;
		case OMP_REDUCTION_OPERATOR:
			out.print(ompReduction2Pretty((OmpReductionNode) node));
			break;
		case ORDINARY_LABEL:
		case SWITCH_LABEL:
			out.print(labelNode2Pretty((LabelNode) node));
			break;
		case PRAGMA:
			pPrintPragma(out, "", (PragmaNode) node);
			break;
		case STATEMENT:
			pPrintStatement(out, "", (StatementNode) node, true, false);
			break;
		case STATIC_ASSERTION:
			pPrintStaticAssertion(out, "", (StaticAssertionNode) node);
			break;
		case TYPE:
			out.print(type2Pretty("", (TypeNode) node, true));
			break;
		case TYPEDEF:
			pPrintTypedefDeclaration(out, "", (TypedefDeclarationNode) node);
			break;
		case VARIABLE_DECLARATION:
			out.print(variableDeclaration2Pretty("",
					(VariableDeclarationNode) node));
			break;
		case SEQUENCE:
			pPrintSequenceNode((SequenceNode<ASTNode>) node, out);
			break;
		case PAIR:
			pPrintPairNode((PairNode<ASTNode, ASTNode>) node, out);
			break;
		default:
			throw new ABCUnsupportedException(
					"the pretty printing of AST node of " + kind
							+ " kind is not supported yet.", node.getSource()
							.getLocation(false));
		}
	}

	private static void pPrintPairNode(PairNode<ASTNode, ASTNode> pair,
			PrintStream out) {
		ASTNode left = pair.getLeft(), right = pair.getRight();

		out.print("(");
		if (left != null)
			prettyPrint(left, out);
		else
			out.print("NULL");
		out.print(",");
		if (right != null)
			prettyPrint(right, out);
		else
			out.print("NULL");
	}

	private static void pPrintSequenceNode(
			SequenceNode<? extends ASTNode> sequence, PrintStream out) {
		int numChildren = sequence.numChildren();
		for (int i = 0; i < numChildren; i++) {
			ASTNode node = sequence.getSequenceChild(i);
			if (i != 0)
				out.print(", ");
			if (node != null)
				prettyPrint(node, out);
		}
	}

	static void prettyPrint(AST ast, PrintStream out, boolean ignoreStdLibs) {
		SequenceNode<BlockItemNode> root = ast.getRootNode();
		int numChildren = root.numChildren();
		String currentFile = null;

		for (int i = 0; i < numChildren; i++) {
			BlockItemNode child = root.getSequenceChild(i);

			if (child != null) {
				String sourceFile = child.getSource().getFirstToken()
						.getSourceFile().getName();

				if (ignoreStdLibs)
					switch (sourceFile) {
					case "assert.h":
					case "cuda.h":
					case "civlc.cvh":
					case "bundle.cvh":
					case "comm.cvh":
					case "concurrency.cvh":
					case "pointer.cvh":
					case "scope.cvh":
					case "seq.cvh":
					case "float.h":
					case "math.h":
					case "mpi.h":
					case "omp.h":
					case "op.h":
					case "pthread.h":
					case "stdarg.h":
					case "stdbool.h":
					case "stddef.h":
					case "stdio.h":
					case "stdlib.h":
					case "string.h":
					case "time.h":
					case "civl-omp.cvh":
					case "civl-mpi.cvh":
					case "civl-cuda.cvh":
					case "civl-omp.cvl":
					case "civl-mpi.cvl":
					case "civl-cuda.cvl":
					case "civlc.cvl":
					case "concurrency.cvl":
					case "stdio-c.cvl":
					case "stdio.cvl":
					case "omp.cvl":
					case "cuda.cvl":
					case "mpi.cvl":
					case "pthread-c.cvl":
					case "pthread.cvl":
					case "math.cvl":
					case "seq.cvl":
					case "string.cvl":
						continue;
					default:
					}
				if (currentFile == null || !currentFile.equals(sourceFile)) {
					int fileLength = sourceFile.length();
					int leftBarLength, rightBarLength;

					rightBarLength = (headerLength - fileLength - 4) / 2;
					leftBarLength = headerLength - fileLength - 4
							- rightBarLength;
					out.print("//");
					printBar(leftBarLength, '=', out);
					out.print(" ");
					out.print(sourceFile);
					out.print(" ");
					printBar(rightBarLength, '=', out);
					out.print("\n");
					currentFile = sourceFile;
				}
				// pPrintExternalDef(out, child);
				pPrintBlockItem(out, "", child);
				out.println();
			}
		}
	}

	private static void printBar(int length, char symbol, PrintStream out) {
		for (int i = 0; i < length; i++)
			out.print(symbol);
	}

	/* *************************** Private Methods ************************* */

	// private static void pPrintExternalDef(PrintStream out,
	// ExternalDefinitionNode extern) {
	// if (extern instanceof AssumeNode) {
	// pPrintAssume(out, "", (AssumeNode) extern);
	// } else if (extern instanceof AssertNode) {
	// pPrintAssert(out, "", (AssertNode) extern);
	// } else if (extern instanceof EnumerationTypeNode) {
	// out.print(enumType2Pretty("", (EnumerationTypeNode) extern));
	// out.print(";");
	// } else if (extern instanceof OrdinaryDeclarationNode) {
	// pPrintOrdinaryDeclaration(out, "", (OrdinaryDeclarationNode) extern);
	// } else if (extern instanceof PragmaNode) {
	// pPrintPragma(out, "", (PragmaNode) extern);
	// } else if (extern instanceof StaticAssertionNode) {
	// pPrintStaticAssertion(out, "", (StaticAssertionNode) extern);
	// out.print(";");
	// } else if (extern instanceof StructureOrUnionTypeNode) {
	// out.print(structOrUnion2Pretty("",
	// (StructureOrUnionTypeNode) extern));
	// out.print(";");
	// } else if (extern instanceof TypedefDeclarationNode) {
	// pPrintTypedefDeclaration(out, "", (TypedefDeclarationNode) extern);
	// out.print(";");
	// } else if (extern instanceof OmpDeclarativeNode) {
	// pPrintOmpDeclarative(out, "", (OmpDeclarativeNode) extern);
	// }
	// out.print("\n");
	// }

	private static void pPrintOmpNode(PrintStream out, String prefix,
			OmpNode ompNode) {
		OmpNodeKind kind = ompNode.ompNodeKind();

		switch (kind) {
		case DECLARATIVE:
			pPrintOmpDeclarative(out, prefix, (OmpDeclarativeNode) ompNode);
		default:// EXECUTABLE
			pPrintOmpStatement(out, prefix, (OmpExecutableNode) ompNode);
		}
	}

	private static StringBuffer structOrUnion2Pretty(String prefix,
			StructureOrUnionTypeNode strOrUnion) {
		StringBuffer result = new StringBuffer();
		String myIndent = prefix + indention;
		SequenceNode<FieldDeclarationNode> fields = strOrUnion
				.getStructDeclList();

		result.append(prefix);
		if (strOrUnion.isStruct())
			result.append("struct ");
		else
			result.append("union ");
		if (strOrUnion.getName() != null)
			result.append(strOrUnion.getName());
		if (fields != null) {
			int numFields = fields.numChildren();

			result.append("{");
			for (int i = 0; i < numFields; i++) {
				FieldDeclarationNode field = fields.getSequenceChild(i);

				result.append("\n");
				if (!(field.getTypeNode() instanceof StructureOrUnionTypeNode))
					result.append(myIndent);
				result.append(fieldDeclaration2Pretty(myIndent, field));
				result.append(";");
			}
			result.append("\n");
			result.append(prefix);
			result.append("}");
		}
		return result;
	}

	private static StringBuffer fieldDeclaration2Pretty(String prefix,
			FieldDeclarationNode field) {
		String type;
		StringBuffer result = new StringBuffer();
		String fieldName = field.getName();

		type = type2Pretty(prefix, field.getTypeNode(), true).toString();
		if (type.endsWith("]")) {
			Pair<String, String> typeResult = processArrayType(type);

			result.append(typeResult.left);
			result.append(" ");
			if (fieldName != null) {
				result.append(" ");
				result.append(fieldName);
			}
			result.append(typeResult.right);
		} else {
			result.append(type);
			if (fieldName != null) {
				result.append(" ");
				result.append(field.getName());
			}
		}
		return result;
	}

	private static void pPrintStaticAssertion(PrintStream out, String prefix,
			StaticAssertionNode assertion) {
		out.print(prefix);
		out.print("(");
		out.print(expression2Pretty(assertion.getExpression()));
		out.print(", \"");
		out.print(assertion.getMessage().getStringRepresentation());
		out.print("\")");
	}

	private static void pPrintPragma(PrintStream out, String prefix,
			PragmaNode pragma) {
		Iterable<CivlcToken> tokens = pragma.getTokens();

		out.print(prefix);
		out.print("#pragma ");
		out.print(pragma.getPragmaIdentifier().name());

		for (CivlcToken token : tokens) {
			out.print(" ");
			out.print(token.getText());
		}
	}

	private static StringBuffer enumType2Pretty(String prefix,
			EnumerationTypeNode enumeration) {
		StringBuffer result = new StringBuffer();
		IdentifierNode tag = enumeration.getTag();
		SequenceNode<EnumeratorDeclarationNode> enumerators = enumeration
				.enumerators();
		String myIndent = prefix + indention;

		result.append(prefix);
		result.append("enum ");
		if (tag != null)
			result.append(tag.name());
		if (enumerators != null) {
			int num = enumerators.numChildren();

			result.append("{");
			for (int i = 0; i < num; i++) {
				EnumeratorDeclarationNode enumerator = enumerators
						.getSequenceChild(i);

				if (i != 0)
					result.append(",");
				result.append("\n");
				result.append(myIndent);
				result.append(enumeratorDeclaration2Pretty(enumerator));
			}
			result.append("\n");
			result.append(prefix);
			result.append("}");
		}
		return result;
	}

	private static StringBuffer enumeratorDeclaration2Pretty(
			EnumeratorDeclarationNode enumerator) {
		StringBuffer result = new StringBuffer();

		result.append(enumerator.getName());
		if (enumerator.getValue() != null) {
			result.append("=");
			result.append(expression2Pretty(enumerator.getValue()));
		}
		return result;
	}

	private static void pPrintOmpDeclarative(PrintStream out, String prefix,
			OmpDeclarativeNode ompDeclarative) {
		OmpDeclarativeNodeKind kind = ompDeclarative.ompDeclarativeNodeKind();

		out.print("#pragma omp ");
		switch (kind) {
		case REDUCTION:
			out.print("reduction");
			break;
		case THREADPRIVATE:
			out.print("threadprivate");
			break;
		default:
			throw new ABCUnsupportedException(
					"The OpenMP declarative directive " + kind
							+ " is not supported yet.", ompDeclarative
							.getSource().getLocation(false));
		}
		out.print("(");
		out.print(sequenceExpression2Pretty(ompDeclarative.variables()));
		out.print(")");
	}

	private static void pPrintFunctionDeclaration(PrintStream out,
			String prefix, FunctionDeclarationNode function) {
		FunctionTypeNode typeNode = function.getTypeNode();
		TypeNode returnType = typeNode.getReturnType();
		SequenceNode<VariableDeclarationNode> paras = typeNode.getParameters();
		int numOfParas = paras.numChildren();
		SequenceNode<ContractNode> contracts = function.getContract();

		if (contracts != null && contracts.numChildren() > 0)
			pPrintContracts(out, prefix, contracts);
		out.print(prefix);
		if (function instanceof AbstractFunctionDefinitionNode)
			out.print("$abstract ");
		if (function.hasGlobalFunctionSpecifier())
			out.print("__global__ ");
		if (function.hasAtomicFunctionSpeciier())
			out.print("$atomic_f ");
		if (function.hasSystemFunctionSpeciier())
			out.print("$system ");
		if (function.hasInlineFunctionSpecifier())
			out.print("inline ");
		if (function.hasNoreturnFunctionSpecifier())
			out.print("_Noreturn ");
		out.print(type2Pretty("", returnType, false));
		out.print(" ");
		out.print(function.getName());
		out.print("(");
		for (int i = 0; i < numOfParas; i++) {
			if (i != 0)
				out.print(", ");
			out.print(variableDeclaration2Pretty("", paras.getSequenceChild(i)));
		}
		if (typeNode.hasVariableArgs())
			out.print(", ...");
		out.print(")");
		// for (int i = 0; i < numContracts; i++) {
		// out.print("\n");
		// pPrintContract(out, prefix + indention,
		// contracts.getSequenceChild(i));
		// }

		if (function instanceof FunctionDefinitionNode) {
			CompoundStatementNode body = ((FunctionDefinitionNode) function)
					.getBody();

			out.print("\n");
			pPrintCompoundStatement(out, prefix + indention, body, true, false);
		} else {
			out.print(";");
		}
	}

	private static void pPrintContracts(PrintStream out, String prefix,
			SequenceNode<ContractNode> contracts) {
		String newLinePrefix = prefix + "\n  @ ";
		int numContracts = contracts.numChildren();
		boolean isFirst = true;

		out.print(prefix);
		out.print("/*@ ");
		for (int i = 0; i < numContracts; i++) {
			ContractNode contract = contracts.getSequenceChild(i);

			if (isFirst)
				isFirst = false;
			else
				out.print(newLinePrefix);
			pPrintContractNode(out, newLinePrefix, contract);
		}
		out.print("\n");
		out.print(prefix);
		out.print("  @*/\n");

	}

	private static void pPrintContractNode(PrintStream out, String prefix,
			ContractNode contract) {
		ContractKind kind = contract.contractKind();

		switch (kind) {
		case ASSUMES: {
			AssumesNode assumes = (AssumesNode) contract;

			out.print("assumes ");
			out.print(expression2Pretty(assumes.getPredicate()));
			out.print(";");
			break;
		}
		case ASSIGNS_READS: {
			AssignsOrReadsNode assignsOrReads = (AssignsOrReadsNode) contract;
			// ExpressionNode condition = assignsOrReads.getCondition();

			if (assignsOrReads.isAssigns())
				out.print("assigns ");
			else
				out.print("reads ");
			pPrintSequenceNode(assignsOrReads.getMemoryList(), out);
			out.print(";");
			break;
		}
		case DEPENDS: {
			DependsNode depends = (DependsNode) contract;

			out.print("depends ");
			out.print(sequenceDependsEvent2Pretty(depends.getEventList()));
			out.print(";");
			break;
		}
		case ENSURES: {
			EnsuresNode ensures = (EnsuresNode) contract;

			out.print("ensures ");
			out.print(expression2Pretty(ensures.getExpression()));
			out.print(";");
			break;
		}
		case GUARDS: {
			GuardsNode guard = (GuardsNode) contract;

			out.print("guards ");
			out.print(expression2Pretty(guard.getExpression()));
			out.print(";");
			break;
		}
		case MPI_COLLECTIVE: {
			MPICollectiveBlockNode colBlock = (MPICollectiveBlockNode) contract;
			String indentedNewLinePrefix = prefix + "  ";

			out.print("\\mpi_collective(");
			out.print(expression2Pretty(colBlock.getMPIComm()));
			out.print("," + colBlock.getCollectiveKind());
			for (ContractNode clause : colBlock.getBody()) {
				pPrintContractNode(out, indentedNewLinePrefix, clause);
			}
			break;
		}
		case REQUIRES: {
			RequiresNode requires = (RequiresNode) contract;

			out.print("requires ");
			out.print(expression2Pretty(requires.getExpression()));
			out.print(";");
			break;
		}
		case BEHAVIOR: {
			BehaviorNode behavior = (BehaviorNode) contract;
			SequenceNode<ContractNode> body = behavior.getBody();
			String indentedNewLinePrefix = prefix + "  ";

			out.print("behavior ");
			out.print(behavior.getName().name());
			out.print(":");
			for (ContractNode clause : body) {
				// out.print("\n");
				out.print(indentedNewLinePrefix);
				pPrintContractNode(out, indentedNewLinePrefix, clause);
			}
			break;
		}
		case INVARIANT: {
			InvariantNode invariant = (InvariantNode) contract;

			if (invariant.isLoopInvariant())
				out.print("loop ");
			out.print("invariant ");
			out.print(expression2Pretty(invariant.getExpression()));
			out.print(";");
			break;
		}
		case PURE: {
			out.print("pure;");
			break;
		}
		default:
			throw new ABCUnsupportedException(
					"pretty printing contract node of " + kind + " kind");
		}

	}

	private static StringBuffer sequenceDependsEvent2Pretty(
			SequenceNode<DependsEventNode> eventList) {
		StringBuffer result = new StringBuffer();
		boolean isFirst = true;

		for (DependsEventNode event : eventList) {
			if (isFirst)
				isFirst = false;
			else
				result.append(", ");
			result.append(dependsEvent2Pretty(event));
		}
		return result;
	}

	private static StringBuffer dependsEvent2Pretty(DependsEventNode event) {
		DependsEventNodeKind kind = event.getEventKind();
		StringBuffer result = new StringBuffer();

		switch (kind) {
		case MEMORY: {
			MemoryEventNode rwEvent = (MemoryEventNode) event;

			if (rwEvent.isRead())
				result.append("\\read");
			else
				result.append("\\write");
			result.append("(");
			result.append(sequenceExpression2Pretty(rwEvent.getMemoryList()));
			result.append(")");
			break;
		}
		case COMPOSITE: {
			CompositeEventNode opEvent = (CompositeEventNode) event;
			EventOperator op = opEvent.eventOperator();

			result.append("(");
			result.append(dependsEvent2Pretty(opEvent.getLeft()));
			result.append(")");
			switch (op) {
			case UNION:
				result.append(" + ");
				break;
			case DIFFERENCE:
				result.append(" - ");
				break;
			case INTERSECT:
				result.append(" & ");
				break;
			default:
				throw new ABCUnsupportedException(
						"pretty printing depends event node with " + kind
								+ " operator");
			}
			result.append("(");
			result.append(dependsEvent2Pretty(opEvent.getRight()));
			result.append(")");
			break;
		}
		case CALL: {
			CallEventNode callEvent = (CallEventNode) event;
			SequenceNode<ExpressionNode> args = callEvent.arguments();

			result.append("\\call(");
			result.append(callEvent.getFunction().getIdentifier().name());
			if (args.numChildren() > 0)
				result.append(", ");
			result.append(sequenceExpression2Pretty(callEvent.arguments()));
			result.append(")");
			break;
		}
		case NOACT:
			result.append("\\noact");
			break;
		case ANYACT:
			result.append("\\anyact");
			break;
		default:
			throw new ABCUnsupportedException(
					"pretty printing depends event node of " + kind + " kind");
		}
		return result;
	}

	@SuppressWarnings("unused")
	private static void pPrintContract(PrintStream out, String prefix,
			ContractNode contract) {
		ContractKind kind = contract.contractKind();

		out.print(prefix);
		switch (kind) {
		case ASSIGNS_READS: {
			AssignsOrReadsNode assignsOrReads = (AssignsOrReadsNode) contract;
			// ExpressionNode condition = assignsOrReads.getCondition();

			if (assignsOrReads.isAssigns())
				out.print("$assigns");
			else
				out.print("$reads");
			// if (condition != null) {
			// out.print(" [");
			// out.print(expression2Pretty(condition));
			// out.print("] ");
			// }
			out.print("{");
			pPrintSequenceNode(assignsOrReads.getMemoryList(), out);
			out.print("}");
			break;
		}
		case DEPENDS: {
			DependsNode depends = (DependsNode) contract;
			// ExpressionNode condition = depends.getCondition();

			out.print("depends");
			// if (condition != null) {
			// out.print(" [");
			// out.print(expression2Pretty(condition));
			// out.print("] ");
			// }
			out.print("{");
			// out.print(sequenceExpression2Pretty(depends.getEventList()));
			out.print("}");
			break;
		}
		case ENSURES: {
			EnsuresNode ensures = (EnsuresNode) contract;

			out.print("$ensures");
			out.print("{");
			out.print(expression2Pretty(ensures.getExpression()));
			out.print("}");
			break;
		}
		case GUARDS: {
			GuardsNode guard = (GuardsNode) contract;

			out.print("$guard");
			out.print("{");
			out.print(expression2Pretty(guard.getExpression()));
			out.print("}");
			break;
		}
		case REQUIRES: {
			RequiresNode requires = (RequiresNode) contract;

			out.print("$requires");
			out.print("{");
			out.print(expression2Pretty(requires.getExpression()));
			out.print("}");
			break;
		}
		default:
			throw new ABCUnsupportedException(
					"pretty printing contract node of " + kind + " kind");
		}
	}

	private static void pPrintCompoundStatement(PrintStream out, String prefix,
			CompoundStatementNode compound, boolean isBody, boolean isSwitchBody) {
		int numChildren = compound.numChildren();
		String myIndent = prefix;
		String myPrefix = prefix;

		if (isBody) {
			myPrefix = prefix.substring(0,
					prefix.length() - 2 > 0 ? prefix.length() - 2 : 0);
			out.print(myPrefix);
		} else {
			out.print(myPrefix);
			myIndent = prefix + indention;
		}
		out.print("{\n");
		for (int i = 0; i < numChildren; i++) {
			BlockItemNode child = compound.getSequenceChild(i);

			if (child != null) {
				if (isSwitchBody && !(child instanceof LabeledStatementNode))
					pPrintBlockItem(out, myIndent + indention, child);
				else
					pPrintBlockItem(out, myIndent, child);
				out.print("\n");
			}
		}
		out.print(myPrefix);
		out.print("}");
	}

	private static void pPrintBlockItem(PrintStream out, String prefix,
			BlockItemNode block) {
		BlockItemKind kind = block.blockItemKind();

		switch (kind) {
		case STATEMENT:
			pPrintStatement(out, prefix, (StatementNode) block, false, false);
			break;
		case ORDINARY_DECLARATION:
			if (block instanceof VariableDeclarationNode) {
				out.print(variableDeclaration2Pretty(prefix,
						(VariableDeclarationNode) block));

				out.print(";");
			} else if (block instanceof FunctionDeclarationNode)
				pPrintFunctionDeclaration(out, prefix,
						(FunctionDeclarationNode) block);
			break;
		case TYPEDEF:
			pPrintTypedefDeclaration(out, prefix,
					(TypedefDeclarationNode) block);
			out.print(";");
			break;
		case ENUMERATION:
			out.print(enumType2Pretty(prefix, (EnumerationTypeNode) block)
					+ ";");
			break;
		case OMP_DECLARATIVE:
			pPrintOmpDeclarative(out, prefix, (OmpDeclarativeNode) block);
			break;
		case PRAGMA:
			pPrintPragma(out, prefix, (PragmaNode) block);
			break;
		case STRUCT_OR_UNION:
			out.print(structOrUnion2Pretty(prefix,
					(StructureOrUnionTypeNode) block));
			out.print(";");
			break;
		default:
			throw new ABCUnsupportedException(
					"pretty print of block item node of " + kind + " kind");
		}
	}

	private static void pPrintTypedefDeclaration(PrintStream out,
			String prefix, TypedefDeclarationNode typedef) {

		out.print(prefix);
		out.print("typedef ");
		out.print(type2Pretty("", typedef.getTypeNode(), true));
		out.print(" ");
		out.print(typedef.getName());
	}

	private static void pPrintStatement(PrintStream out, String prefix,
			StatementNode statement, boolean isBody, boolean isSwitchBody) {
		StatementKind kind = statement.statementKind();

		switch (kind) {
		// case ASSUME:
		// pPrintAssume(out, prefix, (AssumeNode) statement);
		// break;
		// case ASSERT:
		// pPrintAssert(out, prefix, (AssertNode) statement);
		// break;
		case ATOMIC:
			pPrintAtomic(out, prefix, (AtomicNode) statement);
			break;
		case COMPOUND:
			pPrintCompoundStatement(out, prefix,
					(CompoundStatementNode) statement, isBody, isSwitchBody);
			break;
		case EXPRESSION:
			pPrintExpressionStatement(out, prefix,
					(ExpressionStatementNode) statement);
			break;
		case CHOOSE:
			pPrintChooseStatement(out, prefix, (ChooseStatementNode) statement);
			break;
		case CIVL_FOR:
			pPrintCivlForStatement(out, prefix, (CivlForNode) statement);
			break;
		case IF:
			pPrintIf(out, prefix, (IfNode) statement);
			break;
		case JUMP:
			pPrintJump(out, prefix, (JumpNode) statement);
			break;
		case LABELED:
			pPrintLabeled(out, prefix, (LabeledStatementNode) statement);
			break;
		case LOOP:
			pPrintLoop(out, prefix, (LoopNode) statement);
			break;
		case NULL:
			out.print(prefix);
			out.print(";");
			break;
		case OMP:
			pPrintOmpStatement(out, prefix, (OmpExecutableNode) statement);
			break;
		case SWITCH:
			pPrintSwitch(out, prefix, (SwitchNode) statement);
			break;
		case WHEN:
			pPrintWhen(out, prefix, (WhenNode) statement);
			break;
		default:
			throw new ABCUnsupportedException(
					"pretty print of statement node of " + kind + " kind");
		}
	}

	private static void pPrintChooseStatement(PrintStream out, String prefix,
			ChooseStatementNode choose) {
		int numChildren = choose.numChildren();
		String myIndent = prefix + indention;

		out.print(prefix);
		out.println("$choose{");

		for (int i = 0; i < numChildren; i++) {
			StatementNode statement = choose.getSequenceChild(i);

			pPrintStatement(out, myIndent, statement, false, true);
			out.print("\n");
		}
		out.print(prefix);
		out.print("}");
	}

	// private static void pPrintAssert(PrintStream out, String prefix,
	// AssertNode assertNode) {
	// SequenceNode<ExpressionNode> explanation = assertNode.getExplanation();
	//
	// out.print(prefix);
	// out.print("$assert ");
	// out.print(expression2Pretty(assertNode.getCondition()));
	// if (explanation != null) {
	// int numArgs = explanation.numChildren();
	//
	// out.print(" : ");
	// for (int i = 0; i < numArgs; i++) {
	// if (i != 0)
	// out.print(", ");
	// out.print(expression2Pretty(explanation.getSequenceChild(i)));
	// }
	// }
	// out.print(";");
	// }

	private static void pPrintOmpStatement(PrintStream out, String prefix,
			OmpExecutableNode ompStmt) {
		OmpExecutableKind kind = ompStmt.ompExecutableKind();
		SequenceNode<IdentifierExpressionNode> privateList = ompStmt
				.privateList(), firstPrivateList = ompStmt.firstprivateList(), sharedList = ompStmt
				.sharedList(), copyinList = ompStmt.copyinList(), copyPrivateList = ompStmt
				.copyprivateList(), lastPrivateList = ompStmt.lastprivateList();
		SequenceNode<OmpReductionNode> reductionList = ompStmt.reductionList();
		boolean nowait = ompStmt.nowait();
		// String myIndent = prefix + indention;
		StatementNode block = ompStmt.statementNode();

		out.print(prefix);
		out.print("#pragma omp ");
		switch (kind) {
		case PARALLEL:
			pPrintOmpParallel(out, prefix, (OmpParallelNode) ompStmt);
			break;
		case SYNCHRONIZATION:
			pPrintOmpSync(out, prefix, (OmpSyncNode) ompStmt);
			break;
		default: // case WORKSHARING:
			pPrintOmpWorksharing(out, prefix, (OmpWorksharingNode) ompStmt);
			break;
		}
		if (nowait)
			out.print("nowait");
		if (privateList != null) {
			out.print("private(");
			out.print(sequenceExpression2Pretty(privateList));
			out.print(") ");
		}
		if (firstPrivateList != null) {
			out.print("firstprivate(");
			out.print(sequenceExpression2Pretty(firstPrivateList));
			out.print(") ");
		}
		if (sharedList != null) {
			out.print("shared(");
			out.print(sequenceExpression2Pretty(sharedList));
			out.print(") ");
		}
		if (copyinList != null) {
			out.print("copyin(");
			out.print(sequenceExpression2Pretty(copyinList));
			out.print(") ");
		}
		if (copyPrivateList != null) {
			out.print("copyprivate(");
			out.print(sequenceExpression2Pretty(copyPrivateList));
			out.print(") ");
		}
		if (lastPrivateList != null) {
			out.print("lastprivate(");
			out.print(sequenceExpression2Pretty(lastPrivateList));
			out.print(") ");
		}
		if (reductionList != null) {
			out.print(sequenceReduction2Pretty(reductionList));
		}

		if (block != null) {
			out.print("\n");
			pPrintStatement(out, prefix, block, false, false);
		}
	}

	private static void pPrintOmpWorksharing(PrintStream out, String prefix,
			OmpWorksharingNode ompWs) {
		OmpWorksharingNodeKind kind = ompWs.ompWorkshareNodeKind();

		switch (kind) {
		case FOR: {
			OmpForNode forNode = (OmpForNode) ompWs;
			int collapse = forNode.collapse();
			OmpScheduleKind schedule = forNode.schedule();

			out.print("for ");
			if (schedule != OmpScheduleKind.NONE) {
				out.print("schedule(");
				switch (forNode.schedule()) {
				case AUTO:
					out.print("auto");
					break;
				case DYNAMIC:
					out.print("dynamic");
					break;
				case GUIDED:
					out.print("guided");
					break;
				case RUNTIME:
					out.print("runtime");
					break;
				default:// STATIC
					out.print("static");
					break;
				}
				if (forNode.chunkSize() != null) {
					out.print(", ");
					out.print(expression2Pretty(forNode.chunkSize()));
				}
				out.print(") ");
			}
			if (collapse > 1) {
				out.print("collapse(");
				out.print(collapse);
				out.print(") ");
			}
			if (forNode.ordered())
				out.print("ordered ");
			break;
		}
		case SECTIONS:
			out.print("sections ");
			break;
		case SINGLE:
			out.print("single ");
			break;
		default: // case SECTION:
			out.print("section ");
		}
	}

	private static void pPrintOmpSync(PrintStream out, String prefix,
			OmpSyncNode ompSync) {
		OmpSyncNodeKind kind = ompSync.ompSyncNodeKind();

		switch (kind) {
		case MASTER:
			out.print("master ");
			break;
		case CRITICAL:
			out.print("critical");
			if (ompSync.criticalName() != null) {
				out.print("(");
				out.print(ompSync.criticalName().name());
				out.print(")");
			}
			out.print(" ");
			break;
		case BARRIER:
			out.print("barrier ");
			break;
		case FLUSH:
			out.print("flush ");
			if (ompSync.flushedList() != null) {
				out.print("(");
				out.print(sequenceExpression2Pretty(ompSync.flushedList()));
				out.print(")");
			}
			break;
		case OMPATOMIC:
			out.print("atomic ");
			break;
		default:// ORDERED
			out.print("ordered ");
		}
	}

	private static void pPrintOmpParallel(PrintStream out, String prefix,
			OmpParallelNode para) {
		ExpressionNode ifClause = para.ifClause(), numThreads = para
				.numThreads();
		boolean isDefaultShared = para.isDefaultShared();

		out.print("parallel ");
		if (ifClause != null) {
			out.print("if(");
			out.print(expression2Pretty(ifClause));
			out.print(") ");
		}
		if (numThreads != null) {
			out.print("num_threads(");
			out.print(expression2Pretty(numThreads));
			out.print(") ");
		}
		if (isDefaultShared)
			out.print("default(shared) ");
		else
			out.print("default(none) ");
	}

	private static StringBuffer sequenceReduction2Pretty(
			SequenceNode<OmpReductionNode> sequence) {
		StringBuffer result = new StringBuffer();
		int num = sequence.numChildren();

		for (int i = 0; i < num; i++) {
			OmpReductionNode reduction = sequence.getSequenceChild(i);

			result.append(ompReduction2Pretty(reduction));
			if (i < num - 1)
				result.append(" ");
		}
		return result;
	}

	private static StringBuffer ompReduction2Pretty(OmpReductionNode reduction) {
		StringBuffer result = new StringBuffer();

		result.append("reduction(");
		switch (reduction.ompReductionOperatorNodeKind()) {
		case FUNCTION: {
			OmpFunctionReductionNode funcNode = (OmpFunctionReductionNode) reduction;

			result.append(expression2Pretty(funcNode.function()));
			break;
		}
		default: // operator
		{
			OmpSymbolReductionNode symbol = (OmpSymbolReductionNode) reduction;

			switch (symbol.operator()) {
			case PLUSEQ:
				result.append("+");
				break;
			case MINUSEQ:
				result.append("-");
				break;
			case TIMESEQ:
				result.append("*");
				break;
			case BITANDEQ:
				result.append("&");
				break;
			case BITOREQ:
				result.append("|");
				break;
			case BITXOREQ:
				result.append("^");
				break;
			case LAND:
				result.append("&&");
				break;
			case LOR:
				result.append("||");
				break;
			default:
				throw new ABCRuntimeException(
						"Invalid operator for OpenMP reduction: "
								+ symbol.operator(), reduction.getSource()
								.getLocation(false));
			}
		}
		}
		result.append(": ");
		result.append(sequenceExpression2Pretty(reduction.variables()));
		result.append(")");
		return result;
	}

	// private static StringBuffer sequenceExpression2Pretty(
	// SequenceNode<IdentifierExpressionNode> sequence) {
	// StringBuffer result = new StringBuffer();
	// int numExpressions = sequence.numChildren();
	//
	// for (int i = 0; i < numExpressions; i++) {
	// IdentifierExpressionNode expression = sequence.getSequenceChild(i);
	//
	// if (i != 0)
	// result.append(", ");
	// result.append(expression2Pretty(expression));
	// }
	// return result;
	// }
	//
	private static StringBuffer sequenceExpression2Pretty(
			SequenceNode<? extends ExpressionNode> sequence) {
		StringBuffer result = new StringBuffer();
		int numExpressions = sequence.numChildren();

		for (int i = 0; i < numExpressions; i++) {
			ExpressionNode expression = sequence.getSequenceChild(i);

			if (i != 0)
				result.append(", ");
			result.append(expression2Pretty(expression));
		}
		return result;
	}

	private static void pPrintCivlForStatement(PrintStream out, String prefix,
			CivlForNode civlFor) {
		DeclarationListNode vars = civlFor.getVariables();
		int numVars = vars.numChildren();

		out.print(prefix);
		if (civlFor.isParallel())
			out.print("$parfor");
		else
			out.print("$for");
		out.print(" (int ");
		for (int i = 0; i < numVars; i++) {
			if (i != 0)
				out.print(", ");
			out.print(vars.getSequenceChild(i).getName());
		}
		out.print(": ");
		out.print(expression2Pretty(civlFor.getDomain()));
		out.println(")");
		pPrintStatement(out, prefix + indention, civlFor.getBody(), true, false);
	}

	private static void pPrintLoop(PrintStream out, String prefix, LoopNode loop) {
		LoopKind loopKind = loop.getKind();
		StringBuffer condition = new StringBuffer();
		String myIndent = prefix + indention;
		StatementNode bodyNode = loop.getBody();
		SequenceNode<ContractNode> contracts = loop.loopContracts();

		if (contracts != null)
			pPrintContracts(out, prefix, contracts);
		if (loop.getCondition() != null)
			condition = expression2Pretty(loop.getCondition());
		switch (loopKind) {
		case WHILE:
			out.print(prefix);
			out.print("while (");
			out.print(condition);
			out.print(")");
			if (bodyNode == null)
				out.print(";");
			else {
				out.print("\n");
				pPrintStatement(out, myIndent, bodyNode, true, false);

			}
			break;
		case DO_WHILE:
			out.print(prefix);
			out.print("do");
			if (bodyNode == null)
				out.print(";");
			else {
				out.print("\n");
				pPrintStatement(out, myIndent, bodyNode, true, false);
			}
			if (bodyNode != null
					&& !(bodyNode instanceof CompoundStatementNode)) {
				out.print("\n");
				out.print(prefix);
			}
			out.print("while (");
			out.print(condition);
			out.print(");");
			break;
		default: // case FOR:
			pPrintFor(out, prefix, (ForLoopNode) loop);
		}
	}

	private static void pPrintAtomic(PrintStream out, String prefix,
			AtomicNode atomicNode) {
		out.print(prefix);
		if (atomicNode.isAtom())
			out.print("$atom\n");
		else
			out.print("$atomic\n");
		pPrintStatement(out, prefix + indention, atomicNode.getBody(), true,
				false);
	}

	private static void pPrintGoto(PrintStream out, String prefix, GotoNode go2) {
		out.print(prefix);
		out.print("goto ");
		out.print(go2.getLabel().name());
		out.print(";");
	}

	private static void pPrintLabeled(PrintStream out, String prefix,
			LabeledStatementNode labeled) {
		LabelNode label = labeled.getLabel();
		StatementNode statement = labeled.getStatement();
		String myIndent = prefix + indention;

		out.print(prefix);
		out.print(labelNode2Pretty(label));
		out.print("\n");
		pPrintStatement(out, myIndent, statement, true, false);
	}

	private static StringBuffer labelNode2Pretty(LabelNode label) {
		StringBuffer result = new StringBuffer();

		if (label instanceof OrdinaryLabelNode) {
			OrdinaryLabelNode ordinary = (OrdinaryLabelNode) label;
			result.append(ordinary.getName());
			result.append(":");
		} else {
			// switch label
			SwitchLabelNode switchLabel = (SwitchLabelNode) label;
			boolean isDefault = switchLabel.isDefault();

			if (isDefault)
				result.append("default:");
			else {
				result.append("case ");
				result.append(expression2Pretty(switchLabel.getExpression()));
				result.append(":");
			}
		}
		return result;
	}

	private static void pPrintSwitch(PrintStream out, String prefix,
			SwitchNode switchNode) {
		out.print(prefix);
		out.print("switch (");
		out.print(expression2Pretty(switchNode.getCondition()));
		out.println(")");
		pPrintStatement(out, prefix + indention, switchNode.getBody(), true,
				true);
	}

	private static void pPrintJump(PrintStream out, String prefix, JumpNode jump) {
		JumpKind kind = jump.getKind();

		switch (kind) {
		case GOTO:
			pPrintGoto(out, prefix, (GotoNode) jump);
			break;
		case CONTINUE:
			out.print(prefix);
			out.print("continue;");
			break;
		case BREAK:
			out.print(prefix);
			out.print("break;");
			break;
		default: // case RETURN:
			pPrintReturn(out, prefix, (ReturnNode) jump);
		}
	}

	private static void pPrintReturn(PrintStream out, String prefix,
			ReturnNode returnNode) {
		ExpressionNode expr = returnNode.getExpression();

		out.print(prefix);
		out.print("return");
		if (expr != null) {
			out.print(" ");
			out.print(expression2Pretty(expr));
		}
		out.print(";");
	}

	private static void pPrintIf(PrintStream out, String prefix, IfNode ifNode) {
		ExpressionNode condition = ifNode.getCondition();
		StatementNode trueBranch = ifNode.getTrueBranch();
		StatementNode falseBranch = ifNode.getFalseBranch();
		String myIndent = prefix + indention;

		out.print(prefix);
		out.print("if (");
		if (condition != null)
			out.print(expression2Pretty(condition));
		out.print(")");
		if (trueBranch == null)
			out.print(";");
		else {
			out.print("\n");
			pPrintStatement(out, myIndent, trueBranch, true, false);
		}
		if (falseBranch != null) {
			out.print("\n");
			out.print(prefix);
			out.print("else\n");
			pPrintStatement(out, myIndent, falseBranch, true, false);
		}
	}

	private static void pPrintFor(PrintStream out, String prefix,
			ForLoopNode loop) {
		ForLoopInitializerNode init = loop.getInitializer();
		ExpressionNode condition = loop.getCondition();
		ExpressionNode incrementer = loop.getIncrementer();
		StatementNode body = loop.getBody();
		String myIndent = prefix + indention;
		SequenceNode<ContractNode> contracts = loop.loopContracts();

		if (contracts != null)
			pPrintContracts(out, prefix, contracts);
		out.print(prefix);
		out.print("for (");
		if (init != null) {
			if (init instanceof ExpressionNode)
				out.print(expression2Pretty((ExpressionNode) init));
			else if (init instanceof DeclarationListNode)
				out.print(declarationList2Pretty((DeclarationListNode) init));
		}
		out.print("; ");
		if (condition != null) {
			out.print(expression2Pretty(condition));
		}
		out.print("; ");
		if (incrementer != null) {
			out.print(expression2Pretty(incrementer));
		}
		out.print(")");
		if (body == null)
			out.print(";");
		else {
			out.print("\n");
			pPrintStatement(out, myIndent, body, true, false);
		}
	}

	private static StringBuffer declarationList2Pretty(DeclarationListNode list) {
		int num = list.numChildren();
		StringBuffer result = new StringBuffer();

		for (int i = 0; i < num; i++) {
			VariableDeclarationNode var = list.getSequenceChild(i);

			if (var == null)
				continue;
			if (i != 0)
				result.append(", ");
			result.append(variableDeclaration2Pretty("", var));
		}
		return result;
	}

	private static void pPrintExpressionStatement(PrintStream out,
			String prefix, ExpressionStatementNode expr) {
		out.print(prefix);
		out.print(expression2Pretty(expr.getExpression()));
		out.print(";");
	}

	private static void pPrintWhen(PrintStream out, String prefix, WhenNode when) {
		String myIndent = prefix + indention;

		out.print(prefix);
		out.print("$when (");
		out.print(expression2Pretty(when.getGuard()));
		out.print(")\n");
		pPrintStatement(out, myIndent, when.getBody(), true, false);
	}

	static private StringBuffer variableDeclaration2Pretty(String prefix,
			VariableDeclarationNode variable) {
		StringBuffer result = new StringBuffer();
		InitializerNode init = variable.getInitializer();
		TypeNode typeNode = variable.getTypeNode();
		String type;
		String varName = variable.getName();

		result.append(prefix);
		if (typeNode.isInputQualified())
			result.append("$input ");
		if (typeNode.isOutputQualified())
			result.append("$output ");
		if (typeNode.isAtomicQualified())
			result.append("_Atomic ");
		if (typeNode.isConstQualified())
			result.append("const ");
		if (typeNode.isRestrictQualified())
			result.append("restrict ");
		if (typeNode.isVolatileQualified())
			result.append("volatile ");
		if (variable.hasExternStorage())
			result.append("extern ");
		if (variable.hasAutoStorage())
			result.append("auto ");
		if (variable.hasRegisterStorage())
			result.append("register ");
		if (variable.hasStaticStorage())
			result.append("static ");
		if (variable.hasThreadLocalStorage())
			result.append("_Thread_local ");
		if (variable.hasSharedStorage())
			result.append("__shared__ ");
		type = type2Pretty("", typeNode, false).toString();
		if (type.endsWith("]")) {
			Pair<String, String> typeResult = processArrayType(type);

			result.append(typeResult.left);
			result.append(" ");
			if (varName != null) {
				result.append(" ");
				result.append(varName);
			}
			result.append(typeResult.right);
		} else {
			result.append(type);
			if (varName != null) {
				result.append(" ");
				result.append(varName);
			}
		}
		if (init != null) {
			result.append(" = ");
			result.append(initializer2Pretty(init));
		}
		return result;
	}

	// TODO need to be improved for more complicated types
	// currently works for multiple dimension arrays
	// e.g. translating (int [20])[10] into int [10][20]
	private static Pair<String, String> processArrayType(String type) {
		int start = type.indexOf('[');
		String typeSuffix = type.substring(start);
		int length = typeSuffix.length();
		Stack<String> extents = new Stack<>();
		String newSuffix = "";
		String extent = "";

		for (int i = 0; i < length; i++) {
			char current = typeSuffix.charAt(i);

			extent += current;
			if (current == ']') {
				extents.push(extent);
				extent = "";
			}
		}
		while (!extents.empty()) {
			newSuffix += extents.pop();
		}
		return new Pair<>(type.substring(0, start), newSuffix);
	}

	private static StringBuffer initializer2Pretty(InitializerNode init) {
		if (init instanceof CompoundInitializerNode) {
			return compoundInitializer2Pretty((CompoundInitializerNode) init);
		} else if (init instanceof ExpressionNode)
			return expression2Pretty((ExpressionNode) init);
		else
			throw new ABCRuntimeException("Invalid initializer: "
					+ init.toString());
	}

	private static StringBuffer compoundInitializer2Pretty(
			CompoundInitializerNode compound) {
		StringBuffer result = new StringBuffer();
		int numPairs = compound.numChildren();

		result.append("{");
		for (int i = 0; i < numPairs; i++) {
			PairNode<DesignationNode, InitializerNode> pair = compound
					.getSequenceChild(i);
			DesignationNode left = pair.getLeft();
			InitializerNode right = pair.getRight();
			int numDesig = left == null ? 0 : left.numChildren();

			if (i != 0)
				result.append(", ");
			if (numDesig > 0) {
				for (int j = 0; j < numDesig; j++) {
					result.append(designator2Pretty(left.getSequenceChild(j)));
				}
				result.append("=");
			}
			result.append(initializer2Pretty(right));
		}
		result.append("}");
		return result;
	}

	private static StringBuffer designator2Pretty(DesignatorNode designator) {
		StringBuffer result = new StringBuffer();

		if (designator instanceof ArrayDesignatorNode) {
			result.append("[");
			result.append(expression2Pretty(((ArrayDesignatorNode) designator)
					.getIndex()));
			result.append("]");
		} else {// FieldDesignatorNode
			result.append(".");
			result.append(((FieldDesignatorNode) designator).getField().name());
		}
		return result;
	}

	// private static void pPrintAssume(PrintStream out, String prefix,
	// AssumeNode assume) {
	// out.print(prefix);
	// out.print("$assume ");
	// out.print(expression2Pretty(assume.getExpression()));
	// out.print(";");
	// }

	private static StringBuffer expression2Pretty(ExpressionNode expression) {
		StringBuffer result = new StringBuffer();

		if (expression == null)
			return result;

		ExpressionKind kind = expression.expressionKind();

		switch (kind) {
		case ALIGNOF: {
			AlignOfNode align = (AlignOfNode) expression;

			result.append("_Alignof(");
			result.append(type2Pretty("", align.getArgument(), false));
			break;
		}
		case ARROW: {
			ArrowNode arrow = (ArrowNode) expression;

			result.append("(");
			result.append(expression2Pretty(arrow.getStructurePointer()));
			result.append(")");
			result.append("->");
			result.append(arrow.getFieldName().name());
			break;
		}
		case CAST: {
			CastNode cast = (CastNode) expression;
			ExpressionNode arg = cast.getArgument();
			ExpressionKind argKind = arg.expressionKind();
			boolean parenNeeded = true;

			result.append("(");
			result.append(type2Pretty("", cast.getCastType(), false));
			result.append(")");
			if (argKind == ExpressionKind.IDENTIFIER_EXPRESSION
					|| argKind == ExpressionKind.CONSTANT
					|| argKind == ExpressionKind.COMPOUND_LITERAL)
				parenNeeded = false;
			if (parenNeeded)
				result.append("(");
			result.append(expression2Pretty(arg));
			if (parenNeeded)
				result.append(")");
			break;
		}
		case COMPOUND_LITERAL:
			return compoundLiteral2Pretty((CompoundLiteralNode) expression);
		case CONSTANT: {
			String constant = ((ConstantNode) expression)
					.getStringRepresentation();

			if (constant.equals("\\false"))
				constant = "$false";
			else if (constant.equals("\\true"))
				constant = "$true";
			result.append(constant);
			break;
		}
		case DERIVATIVE_EXPRESSION:
			return derivative2Pretty((DerivativeExpressionNode) expression);
		case DOT: {
			DotNode dot = (DotNode) expression;

			result.append(expression2Pretty(dot.getStructure()));
			result.append(".");
			result.append(dot.getFieldName().name());
			break;
		}
		case FUNCTION_CALL:
			return functionCall2Pretty((FunctionCallNode) expression);
			// TODO
			// case GENERIC_SELECTION:
			// break;
		case IDENTIFIER_EXPRESSION:
			result.append(((IdentifierExpressionNode) expression)
					.getIdentifier().name());
			break;
		case MPI_CONTRACT_EXPRESSION:
			result.append(((MPIContractExpressionNode) expression)
					.MPIContractExpressionKind());
			break;
		case OPERATOR:
			return operator2Pretty((OperatorNode) expression);
		case QUANTIFIED_EXPRESSION:
			return quantifiedExpression2Pretty((QuantifiedExpressionNode) expression);
		case REGULAR_RANGE:
			return regularRange2Pretty((RegularRangeNode) expression);
			// TODO
			// case REMOTE_REFERENCE:
			// break;
		case SCOPEOF:
			result.append("$scopeof(");
			result.append(expression2Pretty(((ScopeOfNode) expression)
					.expression()));
			result.append(")");
			break;
		case SIZEOF:
			result.append("sizeof(");
			result.append(sizeable2Pretty(((SizeofNode) expression)
					.getArgument()));
			result.append(")");
			break;
		case SPAWN:
			result.append("$spawn ");
			result.append(functionCall2Pretty(((SpawnNode) expression)
					.getCall()));
			break;
		case CALLS:
			result.append("$calls(");
			result.append(functionCall2Pretty(((CallsNode) expression)
					.getCall()));
			result.append(")");
			break;
		case CONTRACT_VERIFY:
			result.append("$contractVerify ");
			result.append(contractVerify2Pretty(((ContractVerifyNode) expression)));
			result.append(")");
			break;
		case REMOTE_REFERENCE:
			result.append("\\remote(");
			result.append(expression2Pretty(((RemoteExpressionNode) expression)
					.getIdentifierNode()));
			result.append(" , ");
			result.append(expression2Pretty(((RemoteExpressionNode) expression)
					.getProcessExpression()));
			result.append(")");
			break;
		case RESULT:
			result.append("\\result");
			break;
		case STATEMENT_EXPRESSION:
			return statementExpression2Pretty((StatementExpressionNode) expression);
		case NOTHING:
			result.append("\\nothing");
			break;
		case WILDCARD:
			result.append("...");
			break;
		case MEMORY_SET:
			result.append("MEMORY_SET in progress...");
			break;
		default:
			throw new ABCUnsupportedException(
					"pretty print of expression node of " + kind + " kind");
		}
		return result;
	}

	private static StringBuffer statementExpression2Pretty(
			StatementExpressionNode statementExpression) {
		StringBuffer result = new StringBuffer();
		CompoundStatementNode compound = statementExpression
				.getCompoundStatement();

		result.append("(");
		result.append(compound.prettyRepresentation());
		result.append(")");
		return result;
	}

	private static StringBuffer derivative2Pretty(DerivativeExpressionNode deriv) {
		StringBuffer result = new StringBuffer();
		int numPartials = deriv.getNumberOfPartials();
		int numArgs = deriv.getNumberOfArguments();

		result.append("$D[");
		result.append(expression2Pretty(deriv.getFunction()));
		for (int i = 0; i < numPartials; i++) {
			PairNode<IdentifierExpressionNode, IntegerConstantNode> partial = deriv
					.getPartial(i);

			result.append(", {");
			result.append(partial.getLeft().getIdentifier().name());
			result.append(",");
			result.append(partial.getRight().getConstantValue());
			result.append("}");
		}
		result.append("](");
		for (int i = 0; i < numArgs; i++) {
			ExpressionNode arg = deriv.getArgument(i);

			if (i != 0)
				result.append(", ");
			result.append(expression2Pretty(arg));
		}
		result.append(")");
		return result;
	}

	private static StringBuffer quantifiedExpression2Pretty(
			QuantifiedExpressionNode quantified) {
		StringBuffer result = new StringBuffer();
		String quantifier;

		switch (quantified.quantifier()) {
		case FORALL:
			quantifier = "$forall";
			break;
		case EXISTS:
			quantifier = "$exists";
			break;
		default:// UNIFORM
			quantifier = "$uniform";
		}
		result.append(quantifier);
		result.append(" {");
		if (quantified.isRange()) {
			result.append(quantified.variable().getName());
			result.append(" = ");
			result.append(expression2Pretty(quantified.lower()));
			result.append(" .. ");
			result.append(expression2Pretty(quantified.upper()));
		} else {
			result.append(variableDeclaration2Pretty("", quantified.variable()));
			result.append(" | ");
			result.append(expression2Pretty(quantified.restriction()));
		}
		result.append("} ");
		result.append("(");
		result.append(expression2Pretty(quantified.expression()));
		result.append(")");
		return result;
	}

	private static StringBuffer compoundLiteral2Pretty(
			CompoundLiteralNode compound) {
		StringBuffer result = new StringBuffer();
		CompoundInitializerNode list = compound.getInitializerList();
		// int numPairs = list.numChildren();
		TypeNode typeNode = compound.getTypeNode();

		if (typeNode != null) {
			result.append("(");
			result.append(type2Pretty("", compound.getTypeNode(), false));
			result.append(")");
		}
		result.append(compoundInitializer2Pretty(list));

		return result;
	}

	private static StringBuffer regularRange2Pretty(RegularRangeNode range) {
		StringBuffer result = new StringBuffer();
		ExpressionNode step = range.getStep();

		result.append(expression2Pretty(range.getLow()));
		result.append(" .. ");
		result.append(expression2Pretty(range.getHigh()));
		if (step != null) {
			result.append(" # ");
			result.append(expression2Pretty(step));
		}
		return result;
	}

	private static StringBuffer sizeable2Pretty(SizeableNode argument) {
		if (argument instanceof ExpressionNode)
			return expression2Pretty((ExpressionNode) argument);
		return type2Pretty("", (TypeNode) argument, false);
	}

	private static StringBuffer functionCall2Pretty(FunctionCallNode call) {
		int argNum = call.getNumberOfArguments();
		StringBuffer result = new StringBuffer();

		result.append(expression2Pretty(call.getFunction()));
		if (call.getNumberOfContextArguments() > 0) {
			result.append("<<<");
			for (int i = 0; i < call.getNumberOfContextArguments(); i++) {
				if (i > 0)
					result.append(", ");
				result.append(expression2Pretty(call.getContextArgument(i)));
			}
			result.append(">>>");
		}
		result.append("(");
		for (int i = 0; i < argNum; i++) {
			if (i > 0)
				result.append(", ");
			result.append(expression2Pretty(call.getArgument(i)));
		}
		result.append(")");
		return result;
	}

	private static StringBuffer contractVerify2Pretty(ContractVerifyNode call) {
		int argNum = call.getNumberOfArguments();
		StringBuffer result = new StringBuffer();

		result.append(expression2Pretty(call.getFunction()));
		if (call.getNumberOfContextArguments() > 0) {
			result.append("<<<");
			for (int i = 0; i < call.getNumberOfContextArguments(); i++) {
				if (i > 0)
					result.append(", ");
				result.append(expression2Pretty(call.getContextArgument(i)));
			}
			result.append(">>>");
		}
		result.append("(");
		for (int i = 0; i < argNum; i++) {
			if (i > 0)
				result.append(", ");
			result.append(expression2Pretty(call.getArgument(i)));
		}
		result.append(")");
		return result;
	}

	private static StringBuffer operator2Pretty(OperatorNode operator) {
		StringBuffer result = new StringBuffer();
		Operator op = operator.getOperator();
		ExpressionNode argNode0 = operator.getArgument(0);
		ExpressionNode argNode1 = operator.numChildren() > 1 ? operator
				.getArgument(1) : null;
		String arg0 = expression2Pretty(argNode0).toString();
		String arg1 = argNode1 != null ? expression2Pretty(argNode1).toString()
				: null;
		String argWtP0 = arg0, argWtP1 = arg1;

		if (argNode0.expressionKind() == ExpressionKind.OPERATOR)
			argWtP0 = "(" + arg0 + ")";
		if (argNode1 != null
				&& argNode1.expressionKind() == ExpressionKind.OPERATOR)
			argWtP1 = "(" + arg1 + ")";
		switch (op) {
		case ADDRESSOF:
			result.append("&(");
			result.append(arg0);
			result.append(")");
			break;
		case ASSIGN:
			result.append(arg0);
			result.append(" = ");
			result.append(arg1);
			break;
		case HASH:
			result.append(arg0);
			result.append("#");
			result.append(arg1);
			break;
		case BIG_O:
			result.append("$O(");
			result.append(arg0);
			result.append(")");
			break;
		case BITAND:
			result.append(argWtP0);
			result.append(" & ");
			result.append(argWtP1);
			break;
		case BITANDEQ:
			result.append(argWtP0);
			result.append(" &= ");
			result.append(argWtP1);
			break;
		case BITCOMPLEMENT:
			result.append("~");
			result.append(argWtP0);
			break;
		case BITOR:
			result.append(argWtP0);
			result.append(" | ");
			result.append(argWtP1);
			break;
		case BITOREQ:
			result.append(argWtP0);
			result.append(" |= ");
			result.append(argWtP1);
			break;
		case BITXOR:
			result.append(argWtP0);
			result.append(" ^ ");
			result.append(argWtP1);
			break;
		case BITXOREQ:
			result.append(argWtP0);
			result.append(" ^= ");
			result.append(argWtP1);
			break;
		case COMMA:
			result.append(arg0);
			result.append(", ");
			result.append(arg1);
			break;
		case CONDITIONAL:
			result.append(arg0);
			result.append(" ? ");
			result.append(arg1);
			result.append(" : ");
			result.append(expression2Pretty(operator.getArgument(2)));
			break;
		case DEREFERENCE:
			result.append("*");
			result.append(arg0);
			break;
		case DIV:
			result.append(argWtP0);
			result.append(" / ");
			result.append(argWtP1);
			break;
		case DIVEQ:
			result.append(argWtP0);
			result.append(" /= ");
			result.append(argWtP1);
			break;
		case EQUALS:
			result.append(argWtP0);
			result.append(" == ");
			result.append(argWtP1);
			break;
		case GT:
			result.append(argWtP0);
			result.append(" > ");
			result.append(argWtP1);
			break;
		case GTE:
			result.append(argWtP0);
			result.append(" >= ");
			result.append(argWtP1);
			break;
		case IMPLIES:
			result.append(argWtP0);
			result.append(" => ");
			result.append(argWtP1);
			break;
		case LAND:
			result.append(argWtP0);
			result.append(" && ");
			result.append(argWtP1);
			break;
		case LOR:
			result.append(argWtP0);
			result.append(" || ");
			result.append(argWtP1);
			break;
		case LT:
			result.append(argWtP0);
			result.append(" < ");
			result.append(argWtP1);
			break;
		case LTE:
			result.append(argWtP0);
			result.append(" <= ");
			result.append(argWtP1);
			break;
		case MINUS:
			result.append(argWtP0);
			result.append(" - ");
			result.append(argWtP1);
			break;
		case MINUSEQ:
			result.append(argWtP0);
			result.append(" -= ");
			result.append(argWtP1);
			break;
		case MOD:
			result.append(argWtP0);
			result.append(" % ");
			result.append(argWtP1);
			break;
		case MODEQ:
			result.append(argWtP0);
			result.append(" %= ");
			result.append(argWtP1);
			break;
		case NEQ:
			result.append(argWtP0);
			result.append(" != ");
			result.append(argWtP1);
			break;
		case NOT:
			result.append("!");
			result.append(argWtP0);
			break;
		case PLUS:
			result.append(argWtP0);
			result.append(" + ");
			result.append(argWtP1);
			break;
		case PLUSEQ:
			result.append(arg0);
			result.append(" += ");
			result.append(arg1);
			break;
		case POSTDECREMENT:
			result.append(arg0);
			result.append("--");
			break;
		case POSTINCREMENT:
			result.append(arg0);
			result.append("++");
			break;
		case PREDECREMENT:
			result.append("--");
			result.append(arg0);
			break;
		case PREINCREMENT:
			result.append("++");
			result.append(arg0);
			break;
		case SHIFTLEFT:
			result.append(argWtP0);
			result.append(" << ");
			result.append(argWtP1);
			break;
		case SHIFTLEFTEQ:
			result.append(argWtP0);
			result.append(" <<= ");
			result.append(argWtP1);
			break;
		case SHIFTRIGHT:
			result.append(argWtP0);
			result.append(" >> ");
			result.append(argWtP1);
			break;
		case SHIFTRIGHTEQ:
			result.append(argWtP0);
			result.append(" >>= ");
			result.append(argWtP1);
			break;
		case SUBSCRIPT:
			result.append(arg0);
			result.append("[");
			result.append(arg1);
			result.append("]");
			break;
		case TIMES:
			result.append(argWtP0);
			result.append(" * ");
			result.append(argWtP1);
			break;
		case TIMESEQ:
			result.append(argWtP0);
			result.append(" -= ");
			result.append(argWtP1);
			break;
		case UNARYMINUS:
			result.append("-");
			result.append(argWtP0);
			break;
		case UNARYPLUS:
			result.append("+");
			result.append(argWtP0);
			break;
		case VALID:
			result.append("\\valid(");
			result.append(arg0);
			result.append(")");
			break;
		default:
			throw new ABCUnsupportedException(
					"pretty print of operator node of " + op + " kind");
		}
		return result;
	}

	private static StringBuffer type2Pretty(String prefix, TypeNode type,
			boolean isTypeDeclaration) {
		StringBuffer result = new StringBuffer();
		TypeNodeKind kind = type.kind();

		result.append(prefix);
		switch (kind) {
		case ARRAY: {
			ArrayTypeNode arrayType = (ArrayTypeNode) type;
			ExpressionNode extent = arrayType.getExtent();

			// result.append("(");
			result.append(type2Pretty("", arrayType.getElementType(),
					isTypeDeclaration));
			// result.append(")");
			result.append("[");
			if (extent != null)
				result.append(expression2Pretty(extent));
			result.append("]");
		}
			break;
		case DOMAIN: {
			DomainTypeNode domainType = (DomainTypeNode) type;
			ExpressionNode dim = domainType.getDimension();

			result.append("$domain");
			if (dim != null) {
				result.append("(");
				result.append(expression2Pretty(dim));
				result.append(")");
			}
			break;
		}
		case VOID:
			result.append("void");
			break;
		case BASIC:
			result.append(basicType2Pretty((BasicTypeNode) type));
			break;
		case ENUMERATION:
			EnumerationTypeNode enumType = (EnumerationTypeNode) type;

			return enumType2Pretty(prefix, enumType);
			// if (isTypeDeclaration)
			// result.append(enumType2Pretty(prefix, enumType));
			// else {
			// result.append("enum");
			// if (enumType.getIdentifier() != null)
			// result.append(" " + enumType.getIdentifier().name());
			// }
			// break;
		case STRUCTURE_OR_UNION: {
			StructureOrUnionTypeNode strOrUnion = (StructureOrUnionTypeNode) type;

			return structOrUnion2Pretty(prefix, strOrUnion);
			// if (isTypeDeclaration)
			// result.append(structOrUnion2Pretty(prefix, strOrUnion));
			// else {
			// if (strOrUnion.isStruct())
			// result.append("struct ");
			// else
			// result.append("union ");
			// result.append(strOrUnion.getName());
			// }
			// break;
		}
		case POINTER:
			result.append(type2Pretty("",
					((PointerTypeNode) type).referencedType(),
					isTypeDeclaration));
			result.append("*");
			break;
		case TYPEDEF_NAME:
			result.append(((TypedefNameNode) type).getName().name());
			break;
		case SCOPE:
			result.append("$scope");
			break;
		case FUNCTION: {
			FunctionTypeNode funcType = (FunctionTypeNode) type;
			SequenceNode<VariableDeclarationNode> paras = funcType
					.getParameters();
			int i = 0;

			result.append(" (");
			result.append(type2Pretty(prefix, funcType.getReturnType(), false));
			result.append(" (");
			for (VariableDeclarationNode para : paras) {
				if (i != 0)
					result.append(", ");
				result.append(variableDeclaration2Pretty("", para));
				i++;
			}
			result.append(")");
			result.append(")");
			break;
		}
		case RANGE:
			result.append("$range");
			break;
		case TYPEOF:
			result.append("typeof(");
			result.append(expression2Pretty(((TypeofNode) type)
					.getExpressionOperand()));
			result.append(")");
			break;
		default:
			throw new ABCUnsupportedException("pretty print of type node of "
					+ kind + " kind");
		}
		return result;
	}

	private static StringBuffer basicType2Pretty(BasicTypeNode type) {
		StringBuffer result = new StringBuffer();
		BasicTypeKind basicKind = type.getBasicTypeKind();

		switch (basicKind) {
		case BOOL:
			result.append("_Bool");
			break;
		case CHAR:
			result.append("char");
			break;
		case DOUBLE:
			result.append("double");
			break;
		case DOUBLE_COMPLEX:
			result.append("double _Complex");
			break;
		case FLOAT:
			result.append("float");
			break;
		case FLOAT_COMPLEX:
			result.append("float _Complex");
			break;
		case INT:
			result.append("int");
			break;
		case LONG:
			result.append("long");
			break;
		case LONG_DOUBLE:
			result.append("long double");
			break;
		case LONG_DOUBLE_COMPLEX:
			result.append("long double _Complex");
			break;
		case LONG_LONG:
			result.append("long long");
			break;
		case REAL:
			result.append("real");
			break;
		case SHORT:
			result.append("short");
			break;
		case SIGNED_CHAR:
			result.append("signed char");
			break;
		case UNSIGNED:
			result.append("unsigned");
			break;
		case UNSIGNED_CHAR:
			result.append("unsigned char");
			break;
		case UNSIGNED_LONG:
			result.append("unsigned long");
			break;
		case UNSIGNED_LONG_LONG:
			result.append("unsigned long long");
			break;
		case UNSIGNED_SHORT:
			result.append("unsigned short");
			break;
		default:
			throw new ABCUnsupportedException(
					"pretty print of basic type node of " + basicKind + " kind");
		}
		return result;
	}
}
