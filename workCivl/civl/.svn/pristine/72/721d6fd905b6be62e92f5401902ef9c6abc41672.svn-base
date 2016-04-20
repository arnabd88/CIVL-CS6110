/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF;

import java.io.PrintStream;
import java.util.Map;
import java.util.Set;

import edu.udel.cis.vsl.abc.program.IF.Program;
import edu.udel.cis.vsl.civl.model.IF.statement.MallocStatement;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLBundleType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

/**
 * A model of a program.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public interface Model extends Sourceable {

	/**
	 * @return The model factory that created this model.
	 */
	public ModelFactory factory();

	/**
	 * @param name
	 *            The name of this model.
	 */
	public void setName(String name);

	/**
	 * @return The name of this model.
	 */
	public String name();

	/**
	 * @return The set of all functions in the model.
	 */
	public Set<CIVLFunction> functions();

	/**
	 * @return The designated outermost function "System."
	 */
	public CIVLFunction system();

	/**
	 * @param functions
	 *            The set of all functions in the model.
	 */
	public void setFunctions(Set<CIVLFunction> functions);

	/**
	 * @param system
	 *            The designated outermost function "System."
	 */
	public void setSystem(CIVLFunction system);

	/**
	 * @param function
	 *            The function to be added to the model.
	 */
	public void addFunction(CIVLFunction function);

	/**
	 * Get a function based on its name.
	 * 
	 * @param name
	 *            The name of the function.
	 * @return The function with the given name. Null if not found.
	 */
	public CIVLFunction function(String name);

	/**
	 * Print the model.
	 * 
	 * @param out
	 *            The PrintStream used to print the model.
	 * @param isDebug
	 *            True iff the debugigng option is enabled, when more
	 *            information will be printed, such as purely local marks,
	 *            location loops, etc.
	 */
	public void print(PrintStream out, boolean isDebug);

	/**
	 * @param externVariables
	 *            Map of names to variables for all extern variables used in
	 *            this model.
	 */
	public void setExternVariables(Map<String, Variable> externVariables);

	/**
	 * @return Map of names to variables for all extern variables used in this
	 *         model.
	 */
	public Map<String, Variable> externVariables();

	int getNumMallocs();

	MallocStatement getMalloc(int index);

	/**
	 * 
	 * @param queueType
	 *            The queue type used by this model.
	 */
	void setQueueType(CIVLType queueType);

	/**
	 * @param messageType
	 *            The message type used by this model.
	 */
	void setMessageType(CIVLType messageType);

	// /**
	// * @param commType
	// * The comm type used by this model.
	// */
	// void setCommType(CIVLType commType);

	/**
	 * @return The queue type used by this model.
	 */
	CIVLType queueType();

	/**
	 * @return The message type used by this model.
	 */
	CIVLType mesageType();

	// /**
	// * @return The comm type used by this model.
	// */
	// CIVLType commType();

	/**
	 * 
	 * @return The bundle type used by this model.
	 */
	CIVLBundleType bundleType();

	// /**
	// *
	// * @return The gcomm type of by this model
	// */
	// CIVLType gcommType();

	// /**
	// * NULL if there is no communicator operation.
	// *
	// * @param gcommType
	// * The gcomm type used by this model
	// */
	// void setGcommType(CIVLType gcommType);

	void setBundleType(CIVLBundleType type);

	/**
	 * Complete the model. This should be called as the last call for
	 * manipulating the model.
	 */
	void complete();

	// /**
	// * The base type of the pointer type $filesystem; a structure type with
	// * fields (0) scope, and (1) files. Returns NULL if there is no IO
	// * operation.
	// *
	// * @return The base type of the handle <code>$filesystem</code>
	// */
	// CIVLStructOrUnionType basedFilesystemType();
	//
	// void setBasedFilesystemType(CIVLStructOrUnionType type);
	//
	// /**
	// * The CIVL struct type $file, defined in stdio. Returns NULL if there is
	// no
	// * IO operation.
	// *
	// * @return The <code>$file</code> type.
	// */
	// CIVLStructOrUnionType fileType();
	//
	// void setFileType(CIVLStructOrUnionType type);
	//
	// /**
	// * The CIVL type FILE, defined in stdio. Returns NULL if there is no IO
	// * operation.
	// *
	// * @return The <code>FILE</code> type.
	// */
	// CIVLStructOrUnionType FILEtype();
	//
	// void setFILEType(CIVLStructOrUnionType type);
	//
	// /**
	// * NULL if there is no barrier operation.
	// *
	// * @return The base type of the handle $gbarrier
	// */
	// CIVLType gbarrierType();
	//
	// /**
	// * Updates the base type of the $gbarrier handle.
	// *
	// * @param gbarrierType
	// * The type to be used as the base type of the $gbarrier handle.
	// */
	// void setGbarrierType(CIVLType gbarrierType);
	//
	// /**
	// * NULL if there is no barrier operation.
	// *
	// * @return The base type of the handle $barrier.
	// */
	// CIVLType barrierType();
	//
	// /**
	// * Updates the base type of the $barrier handle.
	// *
	// * @param barrierType
	// * The type to be used as the base type of the $barrier handle.
	// */
	// void setBarrierType(CIVLType barrierType);
	//
	// /**
	// * NULL if there is no integer iterator operation.
	// *
	// * @return The base type of the handle $int_iter.
	// */
	// CIVLType intIterType();
	//
	// /**
	// * Updates the base type of the $barrier handle.
	// *
	// * @param intIterType
	// * The type to be used as the base type of the $int_iter handle.
	// */
	// void setIntIterType(CIVLType intIterType);
	//
	// /**
	// * Updates the base type of the $omp_gws handle.
	// *
	// * @param ompGwsType
	// * The type to be used as the base type of the $omp_gws handle.
	// */
	// CIVLType ompGwsType();
	//
	// /**
	// * NULL if there is no omp_gws operation.
	// *
	// * @return The base type of the handle $omp_gws.
	// */
	// void setOmpGwsType(CIVLType ompGwsType);
	//
	// /**
	// * NULL if there is no omp_ws operation.
	// *
	// * @return The base type of the handle $omp_ws.
	// */
	// CIVLType ompWsType();
	//
	// /**
	// * Updates the base type of the $omp_ws handle.
	// *
	// * @param ompWsType
	// * The type to be used as the base type of the $omp_ws handle.
	// */
	// void setOmpWsType(CIVLType ompWsType);

	void setHasFscanf(boolean value);

	boolean hasFscanf();

	Program program();

}
