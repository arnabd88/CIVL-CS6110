package edu.udel.cis.vsl.civl.transform.common;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;

import edu.udel.cis.vsl.abc.FrontEnd;
import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.NodeFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.NodePredicate;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDefinitionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FunctionCallNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.CompoundStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.FunctionTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode;
import edu.udel.cis.vsl.abc.ast.type.IF.ArrayType;
import edu.udel.cis.vsl.abc.ast.type.IF.PointerType;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType.BasicTypeKind;
import edu.udel.cis.vsl.abc.ast.type.IF.StructureOrUnionType;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;
import edu.udel.cis.vsl.abc.parse.IF.CParser;
import edu.udel.cis.vsl.abc.parse.IF.OmpCParser;
import edu.udel.cis.vsl.abc.parse.IF.ParseException;
import edu.udel.cis.vsl.abc.parse.IF.ParseTree;
import edu.udel.cis.vsl.abc.preproc.IF.Preprocessor;
import edu.udel.cis.vsl.abc.preproc.IF.PreprocessorException;
import edu.udel.cis.vsl.abc.token.IF.CToken;
import edu.udel.cis.vsl.abc.token.IF.CTokenSource;
import edu.udel.cis.vsl.abc.token.IF.Formation;
import edu.udel.cis.vsl.abc.token.IF.Macro;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.SourceFile;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.abc.token.IF.TokenFactory;
import edu.udel.cis.vsl.abc.token.IF.TransformFormation;
import edu.udel.cis.vsl.abc.transform.IF.Transformer;
import edu.udel.cis.vsl.civl.config.IF.CIVLConstants;

/**
 * Object used to perform one transformation task. It is instantiated to carry
 * out one invocation of {@link CIVLBaseTransformer#transform(AST)}.
 * 
 * @author siegel
 */
public abstract class BaseWorker {

	protected final static String GEN_MAIN = "_gen_main";
	protected final static String MAIN = "main";
	protected final static String ASSUME = "$assume";
	protected final static String ASSERT = "$assert";
	protected final static String ELABORATE = "$elaborate";

	protected String identifierPrefix;

	/**
	 * The number of new identifiers created by this transformer worker.
	 */
	protected int newIdentifierCounter = 0;

	/**
	 * The name of this transformer, e.g., "OMPtoCIVLTransformer". To be used in
	 * output such as error messages.
	 */
	protected String transformerName;

	/**
	 * The AST factory used by this transformer for all its AST needs.
	 */
	protected ASTFactory astFactory;

	/**
	 * The node factory used by this transformer; same as the node factory
	 * associated to the {@link #astFactory}.
	 */
	protected NodeFactory nodeFactory;

	/**
	 * The token factory used by this transformer; same as the token factory
	 * used by the {@link #astFactory}.
	 */
	protected TokenFactory tokenFactory;

	/* ****************************** Constructor ************************** */

	protected BaseWorker(String transformerName, ASTFactory astFactory) {
		this.transformerName = transformerName;
		this.astFactory = astFactory;
		this.nodeFactory = astFactory.getNodeFactory();
		this.tokenFactory = astFactory.getTokenFactory();
	}

	/* ************************** Protected Methods ************************ */

	/**
	 * Transforms the AST. This is the method that will be invoked to implement
	 * {@link Transformer#transform(AST)}.
	 * 
	 * @param ast
	 *            the given AST to transform
	 * @return the transformed AST, which may or may not == the given one
	 * @throws SyntaxException
	 *             if some statically-detectable error is discovered in the
	 *             process of transformation
	 */
	protected abstract AST transform(AST ast) throws SyntaxException;

	protected StatementNode elaborateCallNode(ExpressionNode argument) {
		FunctionCallNode call = nodeFactory.newFunctionCallNode(
				this.newSource("$elaborate call", CParser.CALL),
				this.identifierExpression(ELABORATE), Arrays.asList(argument),
				null);

		return nodeFactory.newExpressionStatementNode(call);
	}

	/**
	 * Does the root node contains a _main function definition in its children?
	 * 
	 * @return
	 */
	protected boolean has_gen_mainFunction(SequenceNode<BlockItemNode> root) {
		for (BlockItemNode child : root) {
			if (child == null)
				continue;
			if (child instanceof FunctionDefinitionNode) {
				if (((FunctionDefinitionNode) child).getName().equals(GEN_MAIN))
					return true;
			}
		}
		return false;
	}

	/**
	 * Identifies adjacent nodes that are redundant and reduce them to exactly
	 * one node.
	 * 
	 * @param root
	 * @param nodePredicate
	 *            The predicate that if an AST node holds then it will be
	 *            considered as the target one.
	 */
	protected void reduceDuplicateNode(ASTNode root, NodePredicate nodePredicate) {
		int lastIndex = -1;
		int numChildren = root.numChildren();
		// boolean changed = false;

		for (int i = 0; i < numChildren; i++) {
			ASTNode child = root.child(i);

			if (child == null)
				continue;
			reduceDuplicateNode(child, nodePredicate);
			child = root.child(i);
			if (nodePredicate.holds(child)) {
				if (lastIndex >= 0 && lastIndex == i - 1) {
					// this node is identical to the previous node, then remove
					// last node
					root.removeChild(lastIndex);
					// changed = true;
				} else {
					ASTNode previousNonNullChild = this.nonNullChildBefore(
							root, i);

					if (previousNonNullChild != null
							&& (previousNonNullChild instanceof CompoundStatementNode)) {
						CompoundStatementNode previousCompound = (CompoundStatementNode) previousNonNullChild;
						ASTNode lastChildOfPrevious = this
								.getVeryLastItemNodeOfCompoundStatement(previousCompound);

						if (lastChildOfPrevious != null
								&& nodePredicate.holds(lastChildOfPrevious)) {
							lastChildOfPrevious.remove();
						}
					}
				}
				// update last index
				lastIndex = i;
			}
		}
		this.normalizeCompoundStatementNodes(root);
		// if (root.parent() != null) {
		// root.parent().setChild(root.childIndex(),
		// this.normalizeCompoundStatementNodes(root));
		// }
		// if (changed && root.parent() != null) {
		// if (root instanceof CompoundStatementNode) {
		// CompoundStatementNode compoundNode = (CompoundStatementNode) root;
		// List<BlockItemNode> newChildren = new LinkedList<>();
		// int rootIndex = root.childIndex();
		//
		// for (BlockItemNode child : compoundNode) {
		// if (child != null) {
		// child.remove();
		// newChildren.add(child);
		// }
		// }
		// if (newChildren.size() == 1
		// && root.parent() instanceof CompoundStatementNode)
		// root.parent().setChild(rootIndex, newChildren.get(0));
		// else
		// root.parent().setChild(
		// rootIndex,
		// nodeFactory.newCompoundStatementNode(
		// root.getSource(), newChildren));
		// }
		// }
	}

	protected ASTNode nonNullChildBefore(ASTNode node, int index) {
		int numChildren = node.numChildren();

		for (int i = index - 1; i < numChildren && i > 0; i--) {
			ASTNode child = node.child(i);

			if (child != null)
				return child;
		}
		return null;
	}

	protected ASTNode getVeryLastItemNodeOfCompoundStatement(
			CompoundStatementNode compound) {
		int numChildren = compound.numChildren();

		for (int i = numChildren - 1; i >= 0; i--) {
			BlockItemNode child = compound.getSequenceChild(i);

			if (child != null) {
				if (child instanceof CompoundStatementNode)
					return this
							.getVeryLastItemNodeOfCompoundStatement((CompoundStatementNode) child);
				else
					return child;
			}
		}
		return null;
	}

	/**
	 * For a compound statement node, removes any child node that is null or an
	 * empty compound statement node.
	 * 
	 * @param node
	 * @return
	 */
	protected ASTNode normalizeCompoundStatementNodes(ASTNode node) {
		int numChildren = node.numChildren();
		ASTNode newNode = node;

		for (int i = 0; i < numChildren; i++) {
			ASTNode child = node.child(i);

			if (child == null)
				continue;
			normalizeCompoundStatementNodes(child);
		}
		if (node instanceof CompoundStatementNode) {
			List<BlockItemNode> items = new LinkedList<>();
			CompoundStatementNode compound = (CompoundStatementNode) node;

			for (BlockItemNode item : compound) {
				if (item != null
						&& (!(item instanceof CompoundStatementNode) || !this
								.isEmptyCompoundStatementNode((CompoundStatementNode) item))) {
					item.remove();
					items.add(item);
				}
			}
			newNode = nodeFactory.newCompoundStatementNode(node.getSource(),
					items);
			if (node.parent() != null)
				node.parent().setChild(node.childIndex(), newNode);
		}
		return newNode;
	}

	protected boolean isEmptyCompoundStatementNode(
			CompoundStatementNode compound) {
		if (compound.numChildren() == 0)
			return true;
		for (BlockItemNode child : compound) {
			if (child == null)
				continue;
			if (child instanceof CompoundStatementNode) {
				if (isEmptyCompoundStatementNode((CompoundStatementNode) child))
					continue;
			}
			return false;
		}
		return true;
	}

	/**
	 * rename all main function declaration to _main, and all function call to
	 * main to _main.
	 * 
	 * @param root
	 */
	protected void transformMainFunction(SequenceNode<BlockItemNode> root) {
		for (BlockItemNode child : root) {
			if (child == null)
				continue;
			if (child instanceof FunctionDeclarationNode) {
				FunctionDeclarationNode funcDecl = (FunctionDeclarationNode) child;

				if (funcDecl.getName().equals(MAIN)) {
					funcDecl.getIdentifier().setName(GEN_MAIN);
					// FunctionTypeNode funcType = funcDecl.getTypeNode();
					//
					// VariableDeclarationNode secondPara = funcType
					// .getParameters().getSequenceChild(1);

					// secondPara.getTypeNode().setConstQualified(true);
				}
			}
			transformMainCall(child);
		}
	}

	protected void createNewMainFunction(SequenceNode<BlockItemNode> root) {
		FunctionCallNode callMain;
		List<BlockItemNode> blockItems = new LinkedList<>();
		FunctionTypeNode mainFuncType;
		FunctionDefinitionNode newMainFunction;

		callMain = nodeFactory.newFunctionCallNode(
				this.newSource("new main function", CParser.CALL),
				this.identifierExpression(GEN_MAIN),
				new LinkedList<ExpressionNode>(), null);
		blockItems.add(nodeFactory.newExpressionStatementNode(callMain));
		mainFuncType = nodeFactory.newFunctionTypeNode(this.newSource(
				"new main function", CParser.TYPE), nodeFactory
				.newBasicTypeNode(
						this.newSource("new main function", CParser.TYPE),
						BasicTypeKind.INT), nodeFactory.newSequenceNode(this
				.newSource("new main function", CParser.PARAMETER_TYPE_LIST),
				"formal parameter types",
				new LinkedList<VariableDeclarationNode>()), false);
		newMainFunction = nodeFactory.newFunctionDefinitionNode(this.newSource(
				"new main function", CParser.FUNCTION_DEFINITION), this
				.identifier(MAIN), mainFuncType, null, nodeFactory
				.newCompoundStatementNode(
						this.newSource("new main function", CParser.BODY),
						blockItems));
		root.addSequenceChild(newMainFunction);
	}

	/**
	 * rename all calls to main to _main.
	 * 
	 * @param node
	 */
	private void transformMainCall(ASTNode node) {
		if (node instanceof FunctionCallNode) {
			FunctionCallNode call = (FunctionCallNode) node;
			ExpressionNode function = call.getFunction();

			if (function instanceof IdentifierExpressionNode) {
				IdentifierNode functionID = ((IdentifierExpressionNode) function)
						.getIdentifier();

				if (functionID.name().equals(MAIN))
					functionID.setName(GEN_MAIN);
			}
		}
		for (ASTNode child : node.children()) {
			if (child == null)
				continue;
			this.transformMainCall(child);
		}
	}

	protected FunctionDeclarationNode assumeFunctionDeclaration(Source source) {
		IdentifierNode name = nodeFactory.newIdentifierNode(source, "$assume");
		FunctionTypeNode funcType = nodeFactory.newFunctionTypeNode(source,
				nodeFactory.newVoidTypeNode(source), nodeFactory
						.newSequenceNode(source, "Formals", Arrays
								.asList(nodeFactory.newVariableDeclarationNode(
										source, nodeFactory.newIdentifierNode(
												source, "expression"),
										nodeFactory.newBasicTypeNode(source,
												BasicTypeKind.BOOL))))

				, false);

		return nodeFactory.newFunctionDeclarationNode(source, name, funcType,
				null);
	}

	protected FunctionCallNode functionCall(Source source, String name,
			List<ExpressionNode> arguments) {
		return nodeFactory.newFunctionCallNode(source,
				this.identifierExpression(source, name), arguments, null);
	}

	/**
	 * Produces a unique identifier ending with the given name.
	 * 
	 * @param name
	 *            The ending of the new unique identifier.
	 * @return a unique identifier ending with the given name.
	 */
	protected String newUniqueIdentifier(String name) {
		return identifierPrefix + this.newIdentifierCounter++ + "_" + name;
	}

	/**
	 * Produces a unique identifier.
	 * 
	 * @return a unique identifier.
	 */
	protected String newUniqueIdentifierPrefix() {
		return identifierPrefix + this.newIdentifierCounter++;
	}

	/**
	 * parses a certain CIVL library (which resides in the folder text/include)
	 * into an AST.
	 * 
	 * @param filename
	 *            the file name of the library, e.g., civlc.cvh, civlc-omp.cvh,
	 *            etc.
	 * @return the AST of the given library.
	 * @throws SyntaxException
	 */
	protected AST parseSystemLibrary(String filename) throws SyntaxException {
		FrontEnd frontEnd = new FrontEnd();
		Preprocessor preprocessor = frontEnd.getPreprocessor();
		CTokenSource tokenSource;
		ParseTree tree;

		try {
			tokenSource = preprocessor.outputTokenSource(
					new File[] { CIVLConstants.CIVL_INCLUDE_PATH },
					new File[0], new HashMap<String, Macro>(), filename);
			tree = frontEnd.getParser().parse(tokenSource);
		} catch (PreprocessorException | IOException | ParseException e) {
			return null;
		}
		return frontEnd.getASTBuilder().getTranslationUnit(tree);
	}

	/**
	 * Creates a new {@link Source} object to associate to AST nodes that are
	 * invented by this transformer worker.
	 * 
	 * @param method
	 *            any string which identifies the specific part of this
	 *            transformer responsible for creating the new content;
	 *            typically, the name of the method that created the new
	 *            context. This will appear in error message to help isolate the
	 *            source of the new content.
	 * @param text
	 *            the text to be shown for the source which should be some
	 *            informative message about the source
	 * @param tokenType
	 *            the integer code for the type of the token used to represent
	 *            the source; use one of the constants in {@link CParser} or
	 *            {@link OmpCParser}, for example, such as
	 *            {@link CParser#IDENTIFIER}.
	 * @return the new source object
	 */
	protected Source newSource(String method, int tokenType) {
		Formation formation = tokenFactory.newTransformFormation(
				transformerName, method);
		CToken token = tokenFactory.newCToken(tokenType, "inserted text",
				formation);
		Source source = tokenFactory.newSource(token);

		return source;
	}

	/**
	 * This method should be called after the transformer has completed its
	 * transformation; it finds all source objects (in node and the descendants
	 * of node) that were created by this transformer and adds more information
	 * to them. The new information includes the pretty-print textual
	 * representation of the content of that node (and its descendants), and the
	 * precise point in original actual source code where the new content was
	 * inserted.
	 * 
	 * @param node
	 *            a node in the AST being transformed; typically, the root node
	 */
	protected void completeSources(ASTNode node) {
		ASTNode postNode = nextRealNode(node);
		ASTNode preNode = null;

		for (; node != null; node = node.nextDFS()) {
			Source source = node.getSource();

			if (source != null) {
				CToken firstToken = source.getFirstToken();

				if (firstToken != null) {
					Formation formation = firstToken.getFormation();

					if (formation instanceof TransformFormation) {
						TransformFormation tf = (TransformFormation) formation;

						if (transformerName.equals(tf.getLastFile().getName())) {
							CToken preToken = preNode == null ? null : preNode
									.getSource().getLastToken();
							CToken postToken = postNode == null ? null
									: postNode.getSource().getFirstToken();
							String text = node.prettyRepresentation()
									.toString();

							if (text.length() > 20)
								text = text.substring(0, 18) + "...";
							tf.setPreToken(preToken);
							tf.setPostToken(postToken);
							firstToken.setText(text);
						} else {
							if (node == postNode) {
								preNode = postNode;
								postNode = nextRealNode(preNode);
							}
						}
					}
				}
			}
		}
	}

	/**
	 * Creates an identifier node with a given name. The source information of
	 * the new node is automatically constructed using the method
	 * {@link #newSource(String, int)}.
	 * 
	 * @param name
	 *            The name of the identifier.
	 * @return the new identifier node.
	 */
	protected IdentifierNode identifier(String name) {
		return nodeFactory.newIdentifierNode(
				this.newSource("identifier " + name, CParser.IDENTIFIER), name);
	}

	/**
	 * Creates an identifier expression node with a given name. The source
	 * information of the new node is automatically constructed using the method
	 * {@link #newSource(String, int)}.
	 * 
	 * @param name
	 *            The name of the identifier.
	 * @return the new identifier expression node.
	 */
	protected ExpressionNode identifierExpression(String name) {
		Source source = this
				.newSource("identifier " + name, CParser.IDENTIFIER);

		return nodeFactory.newIdentifierExpressionNode(source,
				nodeFactory.newIdentifierNode(source, name));
	}

	/**
	 * Creates an identifier expression node with a given name.
	 * 
	 * @param source
	 *            The source information of the identifier.
	 * @param name
	 *            The name of the identifier.
	 * @return the new identifier expression node.
	 */
	protected ExpressionNode identifierExpression(Source source, String name) {
		return nodeFactory.newIdentifierExpressionNode(source,
				nodeFactory.newIdentifierNode(source, name));
	}

	/**
	 * Creates a variable declaration node with a given name of the specified
	 * type. The sources are created automatically through the method
	 * {@link #newSource(String, int)}.
	 * 
	 * @param name
	 *            The name of the variable
	 * @param type
	 *            The type of the variable
	 * @return the new variable declaration node
	 */
	protected VariableDeclarationNode variableDeclaration(String name,
			TypeNode type) {
		return nodeFactory.newVariableDeclarationNode(this.newSource(
				"variable declaration of " + name, CParser.DECLARATION), this
				.identifier(name), type);
	}

	/**
	 * Creates a variable declaration node with a given name of the specified
	 * type and initializer. The sources are created automatically through the
	 * method {@link #newSource(String, int)}.
	 * 
	 * @param name
	 *            The name of the variable
	 * @param type
	 *            The type of the variable
	 * @param init
	 *            The initializer of the variable
	 * @return the new variable declaration node.
	 */
	protected VariableDeclarationNode variableDeclaration(String name,
			TypeNode type, ExpressionNode init) {
		// String text = type.prettyRepresentation() + " " + name;
		// if (init != null)
		// text = text + " = " + init.prettyRepresentation();
		return nodeFactory.newVariableDeclarationNode(this.newSource(
				"variable declaration of " + name, CParser.DECLARATION), this
				.identifier(name), type, init);
	}

	/**
	 * Creates a constant node of <code>$here</code>, the source of which is
	 * generated automatically using {@link #newSource(String, int)}.
	 * 
	 * @return the new here node.
	 */
	protected ExpressionNode hereNode() {
		return nodeFactory.newHereNode(this.newSource("constant $here",
				CParser.HERE));
	}

	/**
	 * Creates a type node of void type, the source of which is generated
	 * automatically using {@link #newSource(String, int)}.
	 * 
	 * @return the new void type node.
	 */
	protected TypeNode voidType() {
		return nodeFactory.newVoidTypeNode(this.newSource("type void",
				CParser.VOID));
	}

	/**
	 * Creates a type node of a certain basic type kind, the source of which is
	 * generated automatically using {@link #newSource(String, int)}.
	 * 
	 * @param kind
	 *            the specified basic type kind
	 * @return the new basic type node.
	 */
	protected TypeNode basicType(BasicTypeKind kind) {
		String name = "";

		switch (kind) {
		case BOOL:
			name = "_Bool";
			break;
		case CHAR:
			name = "char";
			break;
		case DOUBLE:
		case DOUBLE_COMPLEX:
			name = "double";
			break;
		case FLOAT:
		case FLOAT_COMPLEX:
			name = "float";
			break;
		case INT:
			name = "int";
			break;
		case LONG:
			name = "long";
			break;
		case LONG_DOUBLE:
			name = "long double";
			break;
		case LONG_DOUBLE_COMPLEX:
			name = "long double";
			break;
		case LONG_LONG:
			name = "long long";
			break;
		case REAL:
			name = "real";
			break;
		case SHORT:
			name = "short";
			break;
		case SIGNED_CHAR:
			name = "signed char";
			break;
		case UNSIGNED:
			name = "unsigned";
			break;
		case UNSIGNED_CHAR:
			name = "unsigned char";
			break;
		case UNSIGNED_LONG:
			name = "unsigned long";
			break;
		case UNSIGNED_LONG_LONG:
			name = "unsigned long long";
			break;
		case UNSIGNED_SHORT:
			name = "unsigned short";
		default:
		}
		return this.nodeFactory.newBasicTypeNode(
				this.newSource("type " + name, CParser.TYPE), kind);
	}

	/**
	 * Creates a type node of a given type, the source of which is generated
	 * automatically using {@link #newSource(String, int)}.
	 * 
	 * @param type
	 *            the specified type
	 * @return the new type node.
	 */
	protected TypeNode typeNode(Type type) {
		Source source = this.newSource("type " + type, CParser.TYPE);

		return this.typeNode(source, type);
	}

	/**
	 * Creates a type node of a given type, with the given source.
	 * 
	 * @param source
	 *            The source of the type node
	 * @param type
	 *            the specified type
	 * @return the new type node
	 */
	protected TypeNode typeNode(Source source, Type type) {
		switch (type.kind()) {
		case VOID:
			return nodeFactory.newVoidTypeNode(source);
		case BASIC:
			return nodeFactory.newBasicTypeNode(source,
					((StandardBasicType) type).getBasicTypeKind());
		case OTHER_INTEGER:
			return nodeFactory.newBasicTypeNode(source, BasicTypeKind.INT);
		case ARRAY:
			return nodeFactory.newArrayTypeNode(source,
					this.typeNode(source, ((ArrayType) type).getElementType()),
					((ArrayType) type).getVariableSize().copy());
		case POINTER:
			return nodeFactory.newPointerTypeNode(source, this.typeNode(source,
					((PointerType) type).referencedType()));
		case STRUCTURE_OR_UNION: {
			StructureOrUnionType structOrUnionType = (StructureOrUnionType) type;

			return nodeFactory.newStructOrUnionTypeNode(source,
					structOrUnionType.isStruct(),
					this.identifier(structOrUnionType.getTag()), null);
		}
		default:
		}
		return null;
	}

	/**
	 * Creates a boolean constant node (either <code>$true</code> or
	 * <code>$false</code>), the source of which is generated automatically
	 * using {@link #newSource(String, int)}.
	 * 
	 * @param value
	 *            The value of the boolean constant
	 * @return the new boolean constant node
	 */
	protected ExpressionNode booleanConstant(boolean value) {
		String method = value ? "constant $true" : "constant $false";
		int tokenType = value ? CParser.TRUE : CParser.FALSE;

		return nodeFactory.newBooleanConstantNode(
				this.newSource(method, tokenType), value);
	}

	/**
	 * Creates an integer constant node of the specified value, the source of
	 * which is generated automatically using {@link #newSource(String, int)}.
	 * 
	 * @param value
	 *            The value of the integer constant
	 * @return the new integer constant node
	 */
	protected ExpressionNode integerConstant(int value) throws SyntaxException {
		return nodeFactory.newIntegerConstantNode(
				this.newSource("constant " + value, CParser.INTEGER_CONSTANT),
				Integer.toString(value));
	}

	/**
	 * Combines two ASTs into one, assuming that there are no name conflicts.
	 * 
	 * @param first
	 *            the first AST
	 * @param second
	 *            the second AST
	 * @return
	 * @throws SyntaxException
	 */
	protected AST combineASTs(AST first, AST second) throws SyntaxException {
		SequenceNode<BlockItemNode> rootNode;
		List<BlockItemNode> firstNodes = new ArrayList<>(), secondNodes = new ArrayList<>(), allNodes = new ArrayList<>();
		List<SourceFile> sourceFiles = new ArrayList<>();

		for (BlockItemNode child : first.getRootNode()) {
			if (child != null)
				firstNodes.add(child.copy());
		}
		for (BlockItemNode child : second.getRootNode()) {
			// avoid identical nodes introduced by same "includes"
			if (child != null && !this.existNode(firstNodes, child))
				secondNodes.add(child.copy());
		}
		allNodes.addAll(firstNodes);
		allNodes.addAll(secondNodes);
		sourceFiles.addAll(first.getSourceFiles());
		sourceFiles.addAll(second.getSourceFiles());
		rootNode = this.nodeFactory.newSequenceNode(first.getRootNode()
				.getSource(), "Translation Unit", allNodes);
		return this.astFactory.newAST(rootNode, sourceFiles);
	}

	/**
	 * insert a block item node to a compound statement node at the given index.
	 * 
	 * @param compoundNode
	 * @param node
	 * @return
	 */
	protected CompoundStatementNode insertToCompoundStatement(
			CompoundStatementNode compoundNode, BlockItemNode node, int index) {
		int numChildren = compoundNode.numChildren();
		List<BlockItemNode> nodeList = new ArrayList<>(numChildren + 1);

		for (int i = 0; i < numChildren; i++) {
			BlockItemNode child = compoundNode.getSequenceChild(i);

			if (i == index)
				nodeList.add(node);
			nodeList.add(child);
			compoundNode.removeChild(i);
		}
		if (index >= numChildren)
			nodeList.add(node);
		return nodeFactory.newCompoundStatementNode(compoundNode.getSource(),
				nodeList);
	}

	/* *************************** Private Methods ************************* */

	/**
	 * Checks if a list of nodes contains an equivalent node of a given node.
	 * 
	 * @param nodes
	 *            the list of nodes
	 * @param theNode
	 *            the specified node
	 * @return true iff the list of nodes contains an identical node of the
	 *         specified node.
	 */
	private boolean existNode(List<? extends ASTNode> nodes, ASTNode theNode) {
		for (ASTNode node : nodes) {
			if (node.diff(theNode) == null)
				return true;
		}
		return false;
	}

	/**
	 * Determines whether the given node is a leaf node, i.e., a node with no
	 * non-null children.
	 * 
	 * @param node
	 *            a non-null AST node
	 * @return true iff node is a leaf node
	 */
	private boolean isLeaf(ASTNode node) {
		for (ASTNode child : node.children()) {
			if (child != null)
				return false;
		}
		return true;
	}

	/**
	 * Finds the next node u after the given node, in DFS order, which satisfies
	 * (1) u is a leaf node, and (2) u contains "actual" source (i.e., not
	 * source generated by a transformer).
	 * 
	 * @param node
	 *            any AST node
	 * @return next leaf node whose first token is actual source, or null if
	 *         there is none
	 */
	private ASTNode nextRealNode(ASTNode node) {
		while (true) {
			node = node.nextDFS();
			if (node == null)
				break;
			if (isLeaf(node)) {
				Source source = node.getSource();

				if (source != null) {
					CToken token = source.getFirstToken();

					if (token != null) {
						Formation formation = token.getFormation();

						if (!(formation instanceof TransformFormation))
							break;
					}
				}
			}
		}
		return node;
	}
}
