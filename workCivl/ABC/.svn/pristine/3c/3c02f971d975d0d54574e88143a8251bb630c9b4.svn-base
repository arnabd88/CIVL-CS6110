package edu.udel.cis.vsl.abc.transform.IF;

import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.Map;

import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.entity.IF.Entity;
import edu.udel.cis.vsl.abc.err.IF.ABCRuntimeException;
import edu.udel.cis.vsl.abc.transform.common.CommonNameTransformer;
import edu.udel.cis.vsl.abc.transform.common.CompareCombiner;
import edu.udel.cis.vsl.abc.transform.common.Pruner;
import edu.udel.cis.vsl.abc.transform.common.SideEffectRemover;

/**
 * This class manages the set of transformations provided by an execution of
 * ABC.
 * 
 * It provides a static method {@link #newTransformer(String, ASTFactory)} to
 * create a new transformer instance based on the transformer code. It also
 * provides a method that lists all the known codes.
 * 
 * If you create a new {@link Transformer}, you may edit this file so it knows
 * about your transformer, following the pattern of the others: simply add an
 * entry to array {@link #records}. It is not required for you to do so---your
 * transformer can be used to transform a program whether or not it appears
 * here. The advantage of appearing here is that a switch will be automatically
 * added to the command line interface for all transformers appearing here.
 * 
 * Alternatively, you can add your transformer at runtime using method
 * {@link #addTransform(TransformRecord)}.
 * 
 * @author siegel
 * 
 */
public class Transform {

	private static CompareCombiner compareCombiner = new CompareCombiner();

	/**
	 * A list of the transformers available to the command line interface. Add
	 * one entry here when you create a new transformer, following the same
	 * pattern as the others.
	 */
	private static TransformRecord[] records = new TransformRecord[] {

			new TransformRecord(SideEffectRemover.CODE,
					SideEffectRemover.LONG_NAME,
					SideEffectRemover.SHORT_DESCRIPTION) {
				@Override
				public Transformer create(ASTFactory astFactory) {
					return new SideEffectRemover(astFactory);
				}
			},

			new TransformRecord(Pruner.CODE, Pruner.LONG_NAME,
					Pruner.SHORT_DESCRIPTION) {
				@Override
				public Transformer create(ASTFactory astFactory) {
					return new Pruner(astFactory);
				}
			}

	// add more here.

	};

	/**
	 * Map from transform codes to corresponding records.
	 */
	private static Map<String, TransformRecord> codeToRecord = new LinkedHashMap<>();

	/*
	 * Initializes codeToRecord using the list of hard-wired transforms in array
	 * records.
	 */
	static {
		for (TransformRecord record : records) {
			if (codeToRecord.put(record.code, record) != null)
				throw new ABCRuntimeException("Two transformations named "
						+ record.code);
		}
	}

	/**
	 * Adds a new transform to the collection of known ones. Use this method if
	 * you don't want to hardwire your transform in to the ABC code base. You
	 * will need to create an instance of TransformRecord, for example, in the
	 * anonymous way done above with the built-in transforms. It can be added at
	 * any time but usually it is done in some initialization phase.
	 * 
	 * @param record
	 *            a transform record
	 * @throws ABCRuntimeException
	 *             if there is already a transform with the given code in this
	 *             current collection
	 */
	public static void addTransform(TransformRecord record) {
		if (codeToRecord.put(record.code, record) != null)
			throw new ABCRuntimeException("Two transformations named "
					+ record.code);
	}

	/**
	 * Returns the set of transformer codes.
	 * 
	 * @return the set of transformer codes
	 */
	public static Collection<String> getCodes() {
		return codeToRecord.keySet();
	}

	/**
	 * Returns the short description associated to the given transformer code.
	 * 
	 * @param code
	 *            a transformer code currently in the collection
	 * @return the short description of the transformation
	 * @throws ABCRuntimeException
	 *             if there is no such code in the current collection
	 */
	public static String getShortDescription(String code) {
		TransformRecord record = codeToRecord.get(code);

		if (record == null)
			throw new ABCRuntimeException("No transformation with code " + code);
		return record.shortDescription;
	}

	/**
	 * Returns the long name associated to the given transformer code.
	 * 
	 * @param code
	 *            a transformer code currently in the collection
	 * @return the long name of that transformer, e.g., "MPITransformer"
	 * @throws ABCRuntimeException
	 *             if there is no such code in the current collection
	 */
	public static String getLongName(String code) {
		TransformRecord record = codeToRecord.get(code);

		if (record == null)
			throw new ABCRuntimeException("No transformation with code " + code);
		return record.name;
	}

	/**
	 * Produces a new transformer using the given AST Factory. The kind of
	 * transformer produced is determined by the given code, which is a string.
	 * This string is a short name used to identify the transformer, e.g.,
	 * "prune" for the Pruner. The short name can also be used as a commandline
	 * flag to induce use of that transformer, e.g., "abc -prune foo.c".
	 * 
	 * The given AST Factory become permanently identified with the new
	 * transformer. That transformer can only operate on ASTs that were produced
	 * with the same AST Factory.
	 * 
	 * 
	 * 
	 * @param code
	 *            a short string indicating the kind of transformer to produce
	 * @param astFactory
	 *            the AST factory that will is used to produce all the ASTs upon
	 *            which the new transformer will operate
	 * @return a new transformer instance of the specified kind
	 * @throws ABCRuntimeException
	 *             if there is no such code in the current collection
	 */
	public static Transformer newTransformer(String code, ASTFactory astFactory) {
		TransformRecord record = codeToRecord.get(code);

		if (record == null)
			throw new ABCRuntimeException("No transformation with code " + code);
		return record.create(astFactory);
	}

	/**
	 * Gets the compare combiner for combining two CIVL programs into one which
	 * compares the two for functional equivalence.
	 * 
	 * @return the new compare combiner
	 */
	public static Combiner compareCombiner() {
		return Transform.compareCombiner;
	}

	public static NameTransformer nameTransformer(
			Map<Entity, String> newNameMap, ASTFactory astFactory) {
		return new CommonNameTransformer(newNameMap, astFactory);
	}
}
