package edu.udel.cis.vsl.abc.ast.node.common.declaration;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.IF.DifferenceObject;
import edu.udel.cis.vsl.abc.ast.IF.DifferenceObject.DiffKind;
import edu.udel.cis.vsl.abc.ast.entity.IF.Variable;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.InitializerNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

// child 0: identifier
// child 1: type
// child 2: initializer or null or absent
// child 3: constant alignment specifiers or null or absent
// child 4: type alignment specifiers or null or absent

public class CommonVariableDeclarationNode extends
		CommonOrdinaryDeclarationNode implements VariableDeclarationNode {

	private boolean autoStorage = false;

	private boolean registerStorage = false;

	private boolean threadLocalStorage = false;

	private boolean sharedStorage = false;

	private boolean isRefParameter = true;

	public CommonVariableDeclarationNode(Source source,
			IdentifierNode identifier, TypeNode type) {
		super(source, identifier, type);
	}

	/**
	 * Constructor for declarator-based declarations that are not function
	 * definitions (including function prototypes).
	 * 
	 * @param source
	 * @param identifier
	 * @param type
	 * @param initializer
	 */
	public CommonVariableDeclarationNode(Source source,
			IdentifierNode identifier, TypeNode type,
			InitializerNode initializer) {
		super(source, identifier, type);
		addChild(initializer);
	}

	@Override
	public Variable getEntity() {
		return (Variable) super.getEntity();
	}

	@Override
	public boolean hasAutoStorage() {
		return autoStorage;
	}

	@Override
	public void setAutoStorage(boolean value) {
		autoStorage = value;
	}

	@Override
	public boolean hasRegisterStorage() {
		return registerStorage;
	}

	@Override
	public void setRegisterStorage(boolean value) {
		registerStorage = value;
	}

	@Override
	public InitializerNode getInitializer() {
		if (this.numChildren() >= 3)
			return (InitializerNode) child(2);
		else
			return null;
	}

	@Override
	public void setInitializer(InitializerNode initializer) {
		setChild(2, initializer);
	}

	@Override
	public boolean hasThreadLocalStorage() {
		return threadLocalStorage;
	}

	@Override
	public void setThreadLocalStorage(boolean value) {
		threadLocalStorage = value;
	}

	@Override
	public boolean hasSharedStorage() {
		return sharedStorage;
	}

	@Override
	public void setSharedStorage(boolean value) {
		sharedStorage = value;
	}

	@SuppressWarnings("unchecked")
	@Override
	public SequenceNode<TypeNode> typeAlignmentSpecifiers() {
		if (numChildren() >= 5)
			return (SequenceNode<TypeNode>) child(4);
		else
			return null;
	}

	@Override
	public void setTypeAlignmentSpecifiers(SequenceNode<TypeNode> specifiers) {
		setChild(4, specifiers);
	}

	@SuppressWarnings("unchecked")
	@Override
	public SequenceNode<ExpressionNode> constantAlignmentSpecifiers() {
		if (numChildren() >= 4) {
			ASTNode result = child(3);

			return (SequenceNode<ExpressionNode>) result;
		} else {
			return null;
		}
	}

	@Override
	public void setConstantAlignmentSpecifiers(
			SequenceNode<ExpressionNode> specifiers) {
		setChild(3, specifiers);
	}

	protected void printKind(PrintStream out) {
		out.print("ObjectDeclaration");
	}

	@Override
	protected void printBody(PrintStream out) {
		boolean needSeparator = false;

		printKind(out);
		if (hasExternStorage()) {
			out.print("[");
			out.print("extern");
			needSeparator = true;
		}
		if (hasStaticStorage()) {
			out.print(needSeparator ? ", " : "[");
			out.print("static");
			needSeparator = true;
		}
		if (autoStorage) {
			out.print(needSeparator ? ", " : "[");
			out.print("auto");
			needSeparator = true;
		}
		if (registerStorage) {
			out.print(needSeparator ? ", " : "[");
			out.print("register");
			needSeparator = true;
		}
		if (threadLocalStorage) {
			out.print(needSeparator ? ", " : "[");
			out.print("threadLocal");
			needSeparator = true;
		}
		if (needSeparator)
			out.print("]");
	}

	@Override
	public VariableDeclarationNode copy() {
		InitializerNode initializer = getInitializer();
		CommonVariableDeclarationNode result;
		SequenceNode<ExpressionNode> specifiers = constantAlignmentSpecifiers();
		SequenceNode<TypeNode> typeAlignmentSpecifiers = typeAlignmentSpecifiers();

		if (initializer == null)
			result = new CommonVariableDeclarationNode(getSource(),
					duplicate(getIdentifier()), duplicate(getTypeNode()));
		else
			result = new CommonVariableDeclarationNode(getSource(),
					duplicate(getIdentifier()), duplicate(getTypeNode()),
					duplicate(initializer));
		copyStorage(result);
		result.setAutoStorage(hasAutoStorage());
		result.setRegisterStorage(hasRegisterStorage());
		result.setThreadLocalStorage(hasThreadLocalStorage());
		result.setSharedStorage(hasSharedStorage());
		if (specifiers != null)
			result.setConstantAlignmentSpecifiers(specifiers.copy());
		if (typeAlignmentSpecifiers != null)
			result.setTypeAlignmentSpecifiers(typeAlignmentSpecifiers.copy());
		return result;
	}

	@Override
	public NodeKind nodeKind() {
		return NodeKind.VARIABLE_DECLARATION;
	}

	@Override
	public OrdinaryDeclarationKind ordinaryDeclarationKind() {
		return OrdinaryDeclarationKind.VARIABLE_DECLARATION;
	}

	@Override
	protected DifferenceObject diffWork(ASTNode that) {
		if (that instanceof VariableDeclarationNode) {
			VariableDeclarationNode thatVar = (VariableDeclarationNode) that;

			if (!(this.autoStorage == thatVar.hasAutoStorage()
					&& this.registerStorage == thatVar.hasRegisterStorage() && this.threadLocalStorage == thatVar
						.hasThreadLocalStorage()))
				return new DifferenceObject(this, that, DiffKind.OTHER,
						"different variable declaration auto/register/thread-local specifier");
			else
				return null;
		}
		return new DifferenceObject(this, that);
	}

	@Override
	public boolean isRefParameter() {
		return isRefParameter;
	}

	@Override
	public void setIsRefParameter(boolean isRefParameter) {
		this.isRefParameter = isRefParameter;
	}
}
