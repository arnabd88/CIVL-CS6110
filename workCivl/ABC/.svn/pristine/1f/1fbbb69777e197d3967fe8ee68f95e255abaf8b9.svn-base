package edu.udel.cis.vsl.abc.ast.util;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IntegerConstantNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode;
import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;

/*
 * This class provides support for evaluating certain classes of ABC
 * expressions.   It does this by transforming  ABC expressions to SARL 
 * expressions and evaluating those.
 */
public class ExpressionEvaluator {
	// Record mapping from ABC IDs, defined by their Entity, and the translated SARL representation
	private static Map<String,NumericSymbolicConstant> translateID;
	
	private static SymbolicUniverse universe = SARL.newStandardUniverse();

	public static boolean checkEqualityWithConditions(ExpressionNode o1, ExpressionNode o2, List<ExpressionNode> conditions) {
		/*
		 * Should check that operator nodes are of an integer type
		 */
		//System.out.println("ExpressionEvaluator: "+o1+", "+o2+", "+conditions);
		
		BooleanExpression context = universe.trueExpression();
		Reasoner reasoner = universe.reasoner(context);
		
		translateID = new HashMap<String,NumericSymbolicConstant>();
		
		NumericExpression n1 = toSarlNumeric(o1);
		NumericExpression n2 = toSarlNumeric(o2);
		BooleanExpression equiv = universe.equals(n1, n2);
		
		BooleanExpression current = equiv;
		//System.out.println("ExpressionEvaluator Check "+equiv);

		
		for(ExpressionNode e : conditions) {
			current = universe.and(current, (BooleanExpression) toSarlBool(e));
		}
		
		//System.out.println("ExpressionEvaluator Check with Conditions "+current);
		
		return reasoner.isValid(current);
	}
	
	/*
	 * Visit the operator node and convert it to a SARL expression.
	 * The following are not supported in operator nodes:
	 *   - function calls
	 *   - array references
	 */
		
	private static BooleanExpression toSarlBool(ExpressionNode o) {
		if (o instanceof OperatorNode) {
			OperatorNode op = (OperatorNode) o;
			/*
			 * Works with basic logical and relational operators now.  Could be extended to handle
			 * arrays, etc. (not sure how well that will work, but ...)
			 */
			OperatorNode.Operator oper = op.getOperator();
			if (oper == OperatorNode.Operator.NEQ) {
				return universe.not(toSarlBool(op.getArgument(1)));
			} else if (oper == OperatorNode.Operator.LAND || oper == OperatorNode.Operator.LOR) {
				BooleanExpression op1 = toSarlBool(op.getArgument(0));
				BooleanExpression op2 = toSarlBool(op.getArgument(1));
				switch (oper) {
				case LAND:
					return universe.and(op1,op2);
				case LOR:
					return universe.or(op1,op2);
				default: 
					assert false : "ExpressionEvaluator : cannot translate "+oper+" to SARL";
				}
			} else {
				NumericExpression op1 = toSarlNumeric(op.getArgument(0));
				NumericExpression op2 = toSarlNumeric(op.getArgument(1));

				switch (oper) {
				case LT:
					return universe.lessThan(op1,op2);
				case LTE:
					return universe.lessThanEquals(op1,op2);
				case GT:
					return universe.not(universe.lessThanEquals(op1,op2));
				case GTE:
					return universe.not(universe.lessThan(op1,op2));
				case EQUALS: 
					return universe.equals(op1,op2);
				default: 
					assert false : "ExpressionEvaluator : cannot translate "+oper+" to SARL";
				}
			}

		} else {
			assert false : "ExpressionEvaluator : cannot translate "+o+" to SARL";
		}
		return null;
	}

	
	private static NumericExpression toSarlNumeric(ExpressionNode o) {
		if (o instanceof OperatorNode) {
			OperatorNode op = (OperatorNode) o;

			/*
			 * Works with basic integer operators now.  Could be extended to handle
			 * arrays, etc. (not sure how well that will work, but ...)
			 */
			NumericExpression op1 = (NumericExpression) toSarlNumeric(op.getArgument(0));
			OperatorNode.Operator oper = op.getOperator();
			if (oper == OperatorNode.Operator.UNARYPLUS) {
				return op1;
			} else if (oper == OperatorNode.Operator.UNARYMINUS) {
				return universe.minus(op1);
			} else if (oper == OperatorNode.Operator.SUBSCRIPT) {
				/* 
				 * Handle the case where this expression is an array reference expression.
				 * We use uninterpreted functions for this where the name of the function
				 * is "subscript" and we have parameters for both the base array and index
				 * expressions.   This should work for multi-dimensional arrays.
				 */
				return universe.divide(op1,op1); // TBD change second operand and replace this with subscript
			} else {
				NumericExpression op2 = (NumericExpression) toSarlNumeric(op.getArgument(1));
				switch (oper) {
				case DIV:
					return universe.divide(op1,op2);
				case MINUS:
					return universe.subtract(op1,op2);
				case MOD:
					return universe.modulo(op1,op2);
				case PLUS:
					return universe.add(op1,op2);
				case TIMES: 
					return universe.multiply(op1,op2);
				default: 
					assert false : "ExpressionEvaluator : cannot translate "+oper+" to SARL";
				}
			}

		} else if (o instanceof IntegerConstantNode) {
			return universe.integer(((IntegerConstantNode)o).getConstantValue().getIntegerValue());

		} else if (o instanceof IdentifierExpressionNode) {
			String idName = ((IdentifierExpressionNode)o).getIdentifier().name();
			if (translateID.containsKey(idName)) {
				return translateID.get(idName);
			} else {
				NumericSymbolicConstant idSarl = (NumericSymbolicConstant) universe
						.symbolicConstant(universe.stringObject(idName), universe.integerType());
				translateID.put(idName, idSarl);
				return idSarl;
			}	
		} else {
			assert false : "ExpressionEvaluator : cannot translate "+o+" to SARL";
		}
		return null;
	}

}
