package tlc2.tool;

import java.util.HashSet;

import tla2sany.semantic.ExternalModuleTable;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDefNode;

/**
 * Utility class to manage and clear caches in the module AST.
 * 
 * This addresses issue #891: When operator overrides (Java methods implementing
 * TLA+ operators) are loaded during TLC initialization, they are cached in
 * OpDefNode.toolObject fields. These caches persist across multiple TLC runs
 * in the same JVM, causing incorrect behavior.
 * 
 * This class provides methods to clear those caches to allow clean re-initialization
 * on subsequent TLC runs.
 * 
 * @see TLCGlobals#reset()
 */
public class ModuleASTCacheManager {

	/**
	 * Clears all cached tool objects from the module AST for a given tool ID.
	 * 
	 * This method should be called during TLC reset to clear operator override
	 * caches from OpDefNode objects.
	 * 
	 * @param moduleTable The ExternalModuleTable containing all loaded modules
	 * @param toolId The tool ID for which to clear caches
	 */
	public static void clearModuleASTCache(final ExternalModuleTable moduleTable, final int toolId) {
		if (moduleTable == null) {
			// No modules loaded yet
			return;
		}

		// Iterate through all loaded modules
		final ModuleNode[] modules = moduleTable.getModuleNodes();
		final HashSet<ModuleNode> visited = new HashSet<>();
		
		for (final ModuleNode moduleNode : modules) {
			if (moduleNode != null && !visited.contains(moduleNode)) {
				clearModuleNodeCache(moduleNode, toolId, visited);
			}
		}
	}

	/**
	 * Recursively clears all cached tool objects from a single module node and
	 * any extended modules.
	 * 
	 * @param moduleNode The module node to clear
	 * @param toolId The tool ID for which to clear caches
	 * @param visited Set of already-visited modules to avoid infinite recursion
	 * @return The number of OpDefNode caches cleared
	 */
	private static int clearModuleNodeCache(final ModuleNode moduleNode, final int toolId, 
	                                         final HashSet<ModuleNode> visited) {
		if (moduleNode == null || visited.contains(moduleNode)) {
			return 0;
		}

		visited.add(moduleNode);
		int clearedCount = 0;

		// Clear OpDefNode caches for all operator definitions in this module
		final OpDefNode[] opDefs = moduleNode.getOpDefs();
		for (final OpDefNode opDef : opDefs) {
			if (opDef != null && opDef.getBody() != null) {
				// Clear the cached tool object (operator override implementation)
				final Object oldValue = opDef.getBody().getToolObject(toolId);
				if (oldValue != null) {
					opDef.getBody().setToolObject(toolId, null);
					clearedCount++;
				}
			}
		}

		// Clear caches for extended modules
		final HashSet<ModuleNode> extendedModules = moduleNode.getExtendedModuleSet(true);
		if (extendedModules != null) {
			for (final ModuleNode extendedModule : extendedModules) {
				clearedCount += clearModuleNodeCache(extendedModule, toolId, visited);
			}
		}
		
		return clearedCount;
	}

	/**
	 * Clears all cached tool objects from the module AST accessible from the
	 * root module.
	 * 
	 * This is a convenience method for when you have access to the root module
	 * but not the full ExternalModuleTable.
	 * 
	 * @param rootModule The root module of the specification
	 * @param toolId The tool ID for which to clear caches
	 */
	public static void clearModuleASTCache(final ModuleNode rootModule, final int toolId) {
		if (rootModule == null) {
			return;
		}

		clearModuleNodeCache(rootModule, toolId, new HashSet<>());
	}
}
