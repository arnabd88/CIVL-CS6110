package edu.udel.cis.vsl.abc.ast.node.common.expression;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.List;

import edu.udel.cis.vsl.abc.ast.IF.DifferenceObject;
import edu.udel.cis.vsl.abc.ast.conversion.IF.Conversion;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.common.CommonASTNode;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;
import edu.udel.cis.vsl.abc.ast.value.IF.Value;
import edu.udel.cis.vsl.abc.token.IF.Source;

public abstract class CommonExpressionNode extends CommonASTNode implements
		ExpressionNode {

	private Type initialType;

	/**
	 * Has the constant value for this expression been computed? (It may be
	 * null.) If it has, the constant value is cached in field constantValue.
	 */
	private boolean constantComputed = false;

	/**
	 * If this expression has a constant value, the value may be cached here.
	 */
	private Value constantValue = null;

	private ArrayList<Conversion> conversions = new ArrayList<Conversion>();

	public CommonExpressionNode(Source source, List<? extends ASTNode> arguments) {
		super(source, arguments.iterator());
	}

	public CommonExpressionNode(Source source) {
		super(source);
	}

	public CommonExpressionNode(Source source, ASTNode argument) {
		super(source, argument);
	}

	public CommonExpressionNode(Source source, ASTNode argument0,
			ASTNode argument1) {
		super(source, argument0, argument1);
	}

	public CommonExpressionNode(Source source, ASTNode argument0,
			ASTNode argument1, ASTNode argument2) {
		super(source, argument0, argument1, argument2);
	}
	
	public CommonExpressionNode(Source source, ASTNode argument0,
			ASTNode argument1, ASTNode argument2, ASTNode argument3) {
		super(source, argument0, argument1, argument2, argument3);
	}

	@Override
	public int getNumConversions() {
		return conversions.size();
	}

	@Override
	public Conversion getConversion(int index) {
		return conversions.get(index);
	}

	@Override
	public Type getInitialType() {
		return initialType;
	}

	@Override
	public void setInitialType(Type type) {
		this.initialType = type;
	}

	@Override
	public Type getConvertedType() {
		if (conversions.size() > 0)
			return conversions.get(conversions.size() - 1).getNewType();
		else
			return initialType;
	}

	public boolean constantComputed() {
		return constantComputed;
	}

	public Value getConstantValue() {
		return constantValue;
	}

	public void setConstantValue(Value value) {
		this.constantValue = value;
		this.constantComputed = true;
	}

	protected void printExtras(String prefix, PrintStream out) {
		int numConversions = getNumConversions();
		String typeDescriptor = (initialType == null ? "UNKNOWN" : ""
				+ initialType.toString());

		out.println();
		out.print(prefix + "initial type: " + typeDescriptor);
		if (numConversions > 0) {
			out.println();
			out.print(prefix + "conversions");
			for (int i = 0; i < numConversions; i++) {
				out.println();
				out.print(prefix + "| " + getConversion(i));
			}
		}
		if (constantValue != null) {
			out.println();
			out.print(prefix + "constant value: " + constantValue);
		}
	}

	@Override
	public Type getType() {
		return getConvertedType();
	}

	@Override
	public void addConversion(Conversion conversion) {
		Type lastType = getConvertedType();

		if (lastType == null)
			throw new RuntimeException(
					"Internal error: adding conversion before initial type defined");
		if (!lastType.equals(conversion.getOldType()))
			throw new IllegalArgumentException(
					"Old type of conversion is not last type:\n"
							+ conversion.getOldType() + "\n" + lastType);
		conversions.add(conversion);
	}

	@Override
	public void removeConversions() {
		conversions = new ArrayList<Conversion>();
	}

	@Override
	public NodeKind nodeKind() {
		return NodeKind.EXPRESSION;
	}

	@Override
	protected DifferenceObject diffWork(ASTNode that) {
		if (that instanceof ExpressionNode)
			if (this.expressionKind() == ((ExpressionNode) that)
					.expressionKind())
				return null;
		return new DifferenceObject(this, that);
	}
}
