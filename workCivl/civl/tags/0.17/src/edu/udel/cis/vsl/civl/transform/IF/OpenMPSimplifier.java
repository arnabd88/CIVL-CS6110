package edu.udel.cis.vsl.civl.transform.IF;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.abc.transform.IF.BaseTransformer;
import edu.udel.cis.vsl.civl.transform.common.OpenMPSimplifierWorker;

/**
 * This transformer analyzes OpenMP constructs and converts them to simpler,
 * i.e., less concurrent, instances of constructs.
 * 
 * This transform operates in two phases:
 * 
 * 1) Analyze OpenMP workshares to determine those that are provably
 * thread-independent, i.e., execution of workshares in parallel is guaranteed
 * to compute the same result.
 * 
 * 2) Transform OpenMP constructs based on the analysis results.
 * 
 * TBD: a) support nowait clauses b) support collapse clauses (confirm whether
 * collapse uses variables or the first "k" row indices) c) what is the
 * semantics of a parallel region with no pragma, i.e., do we have to reason
 * about its independence to remove the parallel pragma d) intra-iteration
 * dependences, e.g., x[i] = x[i] + a; e) critical, barrier, master, single and
 * other workshares f) calling sensitive parallel workshare nesting, i.e.,
 * caller has parallel pragma, callee has workshare g) semantics of nowait for
 * that continues to method return h) treatment of omp_ calls, i.e., should we
 * preserve the parallelism since the calls likely depend on it i) detect
 * non-escaping heap data from within a omp pragma context, e.g.,
 * fig4.98-threadprivate.c j) default private/shared when there are explicit
 * shared/private clauses that don't mention the var
 * 
 * 
 * @author dwyer
 * 
 */
public class OpenMPSimplifier extends BaseTransformer {

	public final static String CODE = "omp_simplifier";
	public final static String LONG_NAME = "OpenMPSimplifier";
	public final static String SHORT_DESCRIPTION = "simplifies independent C/OpenMP constructs";

	public OpenMPSimplifier(ASTFactory astFactory) {
		super(CODE, LONG_NAME, SHORT_DESCRIPTION, astFactory);
	}

	@Override
	public AST transform(AST ast) throws SyntaxException {
		return new OpenMPSimplifierWorker(astFactory).transform(ast);
	}

}
