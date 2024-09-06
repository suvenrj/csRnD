package analyser;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import ptg.ObjectNode;
import ptg.PointsToGraph;
import soot.SootField;
import soot.SootMethod;

/**
 * Run the "CreateStackOrdering" once you have the PTG (PointsToGraph) ready
 * If ptgs are not created, this might give an error.
 */
public class StackOrderCreator {
    /**
     * Performs dfs and finds the topological order
     * 
     * @param node      - Starting node of the dfs
     * @param ptg       - Points to graph
     * @param visited   - A visited array to have an idea of dfs
     * @param topoOrder - The final result of the dfs - Topological Order
     */
    static void topologicalSortDfs(
            ObjectNode node,
            PointsToGraph ptg,
            HashSet<ObjectNode> visited,
            ArrayList<ObjectNode> topoOrder) {
        // First mark the node that it's visited
        visited.add(node);

        // Now explore all the edges of "node"
        Map<SootField, Set<ObjectNode>> objectNodesMap = ptg.fields.get(node);
        if (objectNodesMap != null) {
            for (SootField sootField : objectNodesMap.keySet()) {
                for (ObjectNode nextObject : objectNodesMap.get(sootField)) {
                    if (!visited.contains(nextObject)) {
                        topologicalSortDfs(nextObject, ptg, visited, topoOrder);
                    }
                }
            }
        }

        // Finally after exploring all the edges, add into the topological order
        topoOrder.add(node);
    }

    /**
     * Create Stack ordering for each ptg in the Static Analyser
     */
    public static void CreateStackOrdering() {
        // We assumed that the PTGs exist in the StaticAnalyser

        System.out.println("PRIYAM - Starting topological sorting");
        for (SootMethod method : StaticAnalyser.ptgs.keySet()) {
            PointsToGraph ptg = StaticAnalyser.ptgs.get(method);

            // If there are cycles, we simply ignore that edge for now
            // in creating the topological order
            // Topological dfs

            HashSet<ObjectNode> visited = new HashSet<ObjectNode>();
            ArrayList<ObjectNode> topoOrder = new ArrayList<ObjectNode>();

            for (Set<ObjectNode> objectNodeSet : ptg.vars.values()) {
                for (ObjectNode object : objectNodeSet) {
                    if (!visited.contains(object)) {
                        topologicalSortDfs(object, ptg, visited, topoOrder);
                    }
                }
            }

            StaticAnalyser.stackOrders.put(method, topoOrder);
        }
    }
}
