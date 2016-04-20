package edu.udel.cis.vsl.abc.front.c.parse;

import java.util.Stack;

import org.antlr.runtime.CommonToken;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.TokenStream;
import org.antlr.runtime.tree.CommonTree;

import edu.udel.cis.vsl.abc.config.IF.Configurations.Language;
import edu.udel.cis.vsl.abc.err.IF.ABCRuntimeException;
import edu.udel.cis.vsl.abc.front.IF.ParseException;
import edu.udel.cis.vsl.abc.front.IF.Parser;
import edu.udel.cis.vsl.abc.front.IF.PreprocessorRuntimeException;
import edu.udel.cis.vsl.abc.front.IF.RuntimeParseException;
import edu.udel.cis.vsl.abc.front.c.ptree.CParseTree;
import edu.udel.cis.vsl.abc.token.IF.CivlcTokenSource;
import edu.udel.cis.vsl.abc.token.common.CommonCivlcToken;

// why not make static methods of all these?
/**
 * <p>
 * Simple interface for a parser of C programs. It includes a bunch of integer
 * constants which are ID numbers of each kind of token (real or fake) that can
 * occur in a C parse tree.
 * </p>
 * 
 * 
 * @author siegel
 * 
 */
public class CParser implements Parser {
	/**
	 * Kind of parsing rule
	 * 
	 * @author Manchun Zhengs
	 *
	 */
	public static enum RuleKind {
		/**
		 * the rule for translating a translation unit
		 */
		TRANSLATION_UNIT,
		/**
		 * the rule for translating a block item
		 */
		BLOCK_ITEM,
		/**
		 * ACSL contracts
		 */
		CONTRACT
	}

	/* *************************** Constructors *************************** */

	public CParser() {

	}

	/* ********************** Static Helper Methods *********************** */

	/**
	 * <p>
	 * Sets some fields of the tokens that occur in the tree.
	 * </p>
	 * 
	 * <p>
	 * I know ANTLR is supposed to do this but I don't think it does it right.
	 * First, the tokenIndexes are not always what I expect. For some reason,
	 * ANTLR's CommonTokenStream sets the index of the last token (EOF) to be
	 * one higher than it should be, so there is a gap in the indexes between
	 * the penultimate token and the last token. I introduced my own "index"
	 * field to CToken (which extends CommonToken) and set it myself correctly.
	 * </p>
	 * 
	 * <p>
	 * Second, ANTLR is supposed to find the range of tokens spanned by each
	 * node in the tree (by examining all descendants of the node). However:
	 * first, the code that does this uses ANTLR's tokenIndex, and I want to do
	 * it using my index. Second, the ANTLR code is only correct under the
	 * assumption that the token indices are non-decreasing as child index
	 * increases, i.e., the token index of child i is less than or equal to that
	 * of child i+1, for all i, for all nodes. (Hence it only has to examine the
	 * first and last child.) There is no reason that assumption has to hold. So
	 * I compute this correctly (and using CToken indexes) and re-set the
	 * "tokenStartIndex" and "tokenStopIndex" fields of each tree node.
	 * </p>
	 * 
	 * @param tree
	 *            a tree resulting from executing an ANTLR parser
	 */
	private static void postProcessTree(CommonTree tree) {
		initPostProcess(tree);
		completePostProcess(tree);
	}

	/**
	 * Marks all nodes as "not yet visited"---indicating by the magic number
	 * -999 for tokenStartIndex and tokenStopIndex.
	 * 
	 * @param tree
	 */
	private static void initPostProcess(CommonTree tree) {
		int numChildren = tree.getChildCount();

		tree.setTokenStartIndex(-999);
		tree.setTokenStopIndex(-999);
		for (int i = 0; i < numChildren; i++)
			initPostProcess((CommonTree) tree.getChild(i));
	}

	/**
	 * Computes the actual start and stop index of each node in the tree.
	 * 
	 * <p>
	 * If there is no CToken occurring in a node or any of its descendants, the
	 * start and stop index of that node will both be set to -1.
	 * </p>
	 * 
	 * @param tree
	 */
	private static void completePostProcess(CommonTree tree) {
		if (tree.getTokenStartIndex() != -999)
			return;
		else {
			int numChildren = tree.getChildCount();
			CommonToken token = (CommonToken) tree.getToken();
			int min, max;

			if (token instanceof CommonCivlcToken) {
				min = max = ((CommonCivlcToken) token).getIndex();
			} else {
				min = max = -1;
			}
			for (int i = 0; i < numChildren; i++) {
				CommonTree child = (CommonTree) tree.getChild(i);
				int childMin, childMax;

				completePostProcess(child);
				childMin = child.getTokenStartIndex();
				childMax = child.getTokenStopIndex();
				if (childMin >= 0 && (min < 0 || childMin < min))
					min = childMin;
				if (childMax >= 0 && (max < 0 || childMax > max))
					max = childMax;
			}
			tree.setTokenStartIndex(min);
			tree.setTokenStopIndex(max);
		}
	}

	/* ************************* CParser Methods ************************** */

	/**
	 * Returns the ANTLR CommonTree resulting from parsing the input, after some
	 * "post-processing" has been done to the tree to fill in some fields.
	 * 
	 * @return the ANTLR tree that results from parsing
	 * @throws ParseException
	 *             if something goes wrong parsing the input
	 */
	public CParseTree parse(RuleKind rule, CivlcTokenSource tokenSource,
			Stack<ScopeSymbols> symbols) throws ParseException {
		TokenStream stream = new CommonTokenStream(tokenSource);
		CivlCParser parser = new CivlCParser(stream);
		CommonTree root;

		parser.setSymbols_stack(symbols);
		try {
			switch (rule) {
			case TRANSLATION_UNIT:
				try {
					root = (CommonTree) parser.translationUnit().getTree();
				} catch (PreprocessorRuntimeException ex) {
					throw new ParseException(ex.getMessage(), ex.getToken());
				}
				break;
			// case EXTERNAL_DEFINITION:
			// root = (CommonTree) parser.externalDeclaration().getTree();
			// break;
			case BLOCK_ITEM:
				root = (CommonTree) parser.blockItemWithScope().getTree();
				break;
			default:
				throw new ABCRuntimeException("Unreachable");
			}
			postProcessTree(root);
		} catch (RecognitionException e) {
			throw new ParseException(e.getMessage(), e.token);
		} catch (RuntimeParseException e) {
			throw new ParseException(e.getMessage());
		}
		return new CParseTree(Language.CIVL_C, rule, tokenSource, root);
	}

	@Override
	public CParseTree parse(CivlcTokenSource tokenSource) throws ParseException {
		return parse(RuleKind.TRANSLATION_UNIT, tokenSource,
				new Stack<ScopeSymbols>());
	}

}
