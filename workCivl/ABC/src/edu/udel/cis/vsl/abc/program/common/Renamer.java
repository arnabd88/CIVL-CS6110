package edu.udel.cis.vsl.abc.program.common;

import java.util.Map;

import edu.udel.cis.vsl.abc.ast.entity.IF.Entity;
import edu.udel.cis.vsl.abc.ast.entity.IF.ProgramEntity;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;

/**
 * Simple class for renaming entities in an AST. It modifies the nodes, but does
 * not create new nodes. The AST must be analyzed with current entity
 * information.
 * 
 * @author siegel
 * 
 */
public class Renamer {

	/**
	 * Map from entities to new name.
	 */
	private Map<ProgramEntity, String> map;

	/**
	 * Constructs new renamed with given renaming map.
	 * 
	 * @param map
	 */
	public Renamer(Map<ProgramEntity, String> map) {
		this.map = map;
	}

	/**
	 * Performs renaming on given node and all its descendants. If the node is
	 * an identifier node and entity associated to that identifier occurs as a
	 * key in the map, the name of the identifier is set to the new name. Method
	 * is called recursively on the children nods.
	 * 
	 * @param node
	 *            a node in the AST
	 */
	public void renameFrom(ASTNode node) {
		if (node instanceof IdentifierNode) {
			IdentifierNode inode = (IdentifierNode) node;
			Entity entity = inode.getEntity();
			String newName = map.get(entity);

			if (newName != null) {
				inode.setName(newName);
			}
		} else {
			for (ASTNode child : node.children())
				if (child != null)
					renameFrom(child);
		}
	}
}
