package resolver;

import Inlining.InlineCheck;
import config.StoreEscape;
import es.CallSite;
import es.ConditionalValue;
import es.ContextualEscapeStatus;
import es.Escape;
import es.EscapeState;
import es.EscapeStatus;
import es.NoEscape;
import ownership.*;
import ptg.ObjectNode;
import ptg.ObjectType;
import ptg.PointsToGraph;
import soot.SootMethod;
import soot.*;
import soot.jimple.InvokeExpr;
import soot.jimple.internal.*;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;

import java.util.*;

public class OwnershipResolverV2 {
    // need to evaluate private/public for these Data structures
    /* Tip: The keySet of existingSummaries is the set of user defined functions*/
    public static Map<SootMethod,HashMap<ObjectNode, EscapeStatus>> existingSummaries; // from static analyser
    private static Map<SootMethod,PointsToGraph> ptgs; // to store method ptgs
    public static HashMap<SootMethod,HashMap<ObjectNode, HashSet<SootMethod>>> solvedSummaries; // non contextual ownership list
    public static HashMap<SootMethod,HashMap<ObjectNode, ContextualOwnershipStatus>> solvedContextualSummaries; // 1-level contextual ownership list
    List<SootMethod> noBCIMethods; // methods from where we need to consider an object escaping
    private static Map<SootMethod, Integer> methodToSccIndex;
    private static Map<Integer, Set<Integer>> sccDag;
    private static Map<Integer, ArrayList<SootMethod>> sccIndexToMethod;
    public static HashMap<SootMethod,HashMap<ObjectNode, HashSet<Integer>>> solvedSummariesSCC;
    Map<Integer, Map<Integer, Integer>> distances;
    Map<Integer, Integer> sccObjCount;
    private static CallGraph cg;
    private static SootMethod globalMethod;
    //public static HashMap<SootMethod,HashMap<ObjectNode, ContextualOwnershipStatus>> solvedContextualSummariesSCC;


    public OwnershipResolverV2(Map<SootMethod, HashMap<ObjectNode, EscapeStatus>> existingSummaries, Map<SootMethod, PointsToGraph> ptgs, List<SootMethod> escapingMethods){
        // initialization of data structures
        OwnershipResolverV2.existingSummaries = existingSummaries;
        OwnershipResolverV2.ptgs = ptgs;
        this.noBCIMethods = escapingMethods;
        solvedContextualSummaries = new HashMap<>();
        solvedSummaries = new HashMap<>();
        methodToSccIndex = new HashMap<>();
        sccIndexToMethod = new HashMap<>();
        sccDag = new HashMap<>();
        solvedSummariesSCC = new HashMap<>();
        distances = new HashMap<>();
        sccObjCount = new HashMap<>();
        cg = Scene.v().getCallGraph();
        globalMethod = null;

        for (Map.Entry<SootMethod, HashMap<ObjectNode, EscapeStatus>> entry : existingSummaries.entrySet()) {
            SootMethod method = entry.getKey();
            solvedContextualSummaries.put(method, new HashMap<>());
            solvedSummaries.put(method, new HashMap<>());
            solvedSummariesSCC.put(method, new HashMap<>());
        }
        // Compute sccDag and methodToSccIndex
        StronglyConnectedMethods();
        // Compute the solvedSummaries and solvedContextualSummaries Data Structures
        AddCallerSummaries();
        // System.out.println(sccDag.keySet().size());
        // System.out.println(solvedSummaries.keySet().size());
        // System.out.println(methodToSccIndex.keySet().size());
        // Compute inter SCC distances
        //getInterSCCDistance();
        // Compute the solvedSummariesSCC Data Structure
        getSCCSummary();
        // Get SCC statistics
        getSCCStats();
        // for (SootMethod key: solvedContextualSummaries.keySet()){
        //     for(ObjectNode obj: solvedContextualSummaries.get(key).keySet()){
        //         System.out.println(key.toString()+" "+obj.toString());
        //         ContextualOwnershipStatus temp = solvedContextualSummaries.get(key).get(obj);
        //         for (CallSite c: temp.ownershipMap.keySet()){
        //             System.out.println(c);
        //             for (SootMethod m: temp.ownershipMap.get(c)){
        //                 System.out.println(m);
        //             }
        //         }
        //     }
        // }

    }
    //helper functions
    /* Function to get solvedSummariesSCC from solvedSummaries*/
    private void getSCCSummary(){
        for (SootMethod key: solvedSummaries.keySet()){
            HashSet<Integer> allSCCIndices = new HashSet<>();
            for (ObjectNode obj: solvedSummaries.get(key).keySet()){
                allSCCIndices.clear();
                for (SootMethod m: solvedSummaries.get(key).get(obj)){
                   allSCCIndices.add(methodToSccIndex.get(m));
                }
                HashSet<Integer> TopSCCIndices = getIndependentNodes(allSCCIndices);
                solvedSummariesSCC.get(key).put(obj, TopSCCIndices);
            }
        }
    }

    /* Function to get SCC related Stats*/
    private void getSCCStats(){
        for(Integer sccInd: sccDag.keySet()){
            sccObjCount.put(sccInd, 0);
        }
        int totalStaticObjects = 0;
        int affectedStaticObjects = 0;
        int stackObjects = 0;
        int heapObjects = 0;
        for (SootMethod key: solvedSummaries.keySet()){
            for (ObjectNode obj: solvedSummaries.get(key).keySet()){
                // only internal objects to be considered
                if (obj.type != ObjectType.internal){
                    continue;
                }
                totalStaticObjects++;
                // ignore stack-allocatable objects
                if (solvedSummaries.get(key).get(obj).size()==1){
                    stackObjects++;
                    continue;
                }
                // ignore objects that have to be allocated on heap
                boolean flag=false;
                for (SootMethod m: solvedSummaries.get(key).get(obj)){
                    if (m.isEntryMethod()){
                        flag=true;
                        heapObjects++;
                        break;
                    }
                }
                if (flag){
                    continue;
                }
                affectedStaticObjects++;
                System.out.println(key.toString()+" "+obj.toString());
                // System.out.println();
                // for (SootMethod m: solvedSummaries.get(key).get(obj)){
                //     System.out.println(m+" "+methodToSccIndex.get(m));
                // }
                System.out.println();
                try{
                    //float avgDist = 0;
                    //int numAncestors = solvedSummariesSCC.get(key).get(obj).size();
                    for (int sccInd : solvedSummariesSCC.get(key).get(obj)){
                        //avgDist+=distances.get(sccInd).get(methodToSccIndex.get(key));
                        sccObjCount.put(sccInd, sccObjCount.get(sccInd)+1);
                    }
                    //System.out.println(avgDist/numAncestors);
                }
                catch(Exception e){
                    System.out.println(e);
                }
                System.out.println();
            }
        }
        int nonZeroSCC = 0;
        int totalSCC=sccObjCount.keySet().size();
        for(Integer sccInd: sccObjCount.keySet()){
            if (sccObjCount.get(sccInd)!=0){
                nonZeroSCC+=1;
                System.out.println(sccInd + ": " + sccObjCount.get(sccInd));
            }
        }
        System.out.println("Total SCCs: " + totalSCC);
        System.out.println("Core SCCs: " + nonZeroSCC);
        System.out.println("Special Memory Region Object Count: " + affectedStaticObjects);
        System.out.println("Stack Object Count: " + stackObjects);
        System.out.println("Heap Object Count: " + heapObjects);
        System.out.println("Total Object Count: " + totalStaticObjects);
    }

    public static List<ObjectNode> GetObjects(Unit u, int num, SootMethod src, List<SootField> fieldList) {
        List<ObjectNode> objs = new ArrayList<>();
        InvokeExpr expr;
        if (u instanceof JInvokeStmt) {
            expr = ((JInvokeStmt) u).getInvokeExpr();
        } else if (u instanceof JAssignStmt) {
            expr = (InvokeExpr) (((JAssignStmt) u).getRightOp());
        } else {
            return null;
        }
        Value arg = null;
        try {
            if (num >= 0) {
                if(expr.getArgCount() > num)
                    arg = expr.getArg(num);
            } else if (num == -1 && (expr instanceof AbstractInstanceInvokeExpr)) {
                arg = ((AbstractInstanceInvokeExpr) expr).getBase();
            }
            else return null;

        } catch (Exception e) {
            System.err.println(u + " " + num + " " + expr);
            Iterator<Edge> iter = cg.edgesOutOf(u);
            while (iter.hasNext()) {
                Edge edg = iter.next();
                System.err.println("EXT: " + edg.tgt() + " " + edg.kind());
            }
            throw e;
        }

        if(arg!= null) {
            if (!(arg instanceof Local))
                return objs;
            else if (((Local) arg).getType() instanceof PrimType)
                return objs;
        }
        try {
            if(ptgs.containsKey(src)) {
                if (ptgs.get(src).vars.containsKey(arg)) {
                    for (ObjectNode o : ptgs.get(src).vars.get(arg)) {
                        if (fieldList != null) {
                            Set<ObjectNode> obj = new HashSet<>();
                            Set<ObjectNode> obj1 = new HashSet<>();
                            obj1.add(o);
                            for (SootField f : fieldList) {
                                obj = getfieldObject(src, obj1, f);
                                if (obj.isEmpty()) {
                                    return null;
                                }
                                obj1 = obj;
                            }
                            if (obj != null) {
                                objs.addAll(obj);
                                return objs;
                            } else {
                                return null;
                            }

                        } else {
                            objs.add(o);
                        }
                    }
                }
            }
        } catch (Exception e) {
            e.printStackTrace();
            System.exit(0);
        }
        return objs;
    }
    //helper functions
    public static List<ObjectNode> GetParmObjects(ObjectNode ob, int num, SootMethod tgt, List<SootField> fieldList) {
        List<ObjectNode> objs = new ArrayList<>();
        try {
            if (fieldList != null) {
                if(ptgs.containsKey(tgt)) {
                    if (ptgs.get(tgt).fields.containsKey(ob)) {
                        Set<ObjectNode> obj = new HashSet<>();
                        Set<ObjectNode> obj1 = new HashSet<>();
                        obj1.add(ob);
                        for (SootField f : fieldList) {
                            obj = getfieldObject(tgt, obj1, f);
                            if (obj.isEmpty()) {
                                return null;
                            }
                            obj1 = obj;
                        }
                        if (obj != null) {
                            objs.addAll(obj);
                            return objs;
                        } else {
                            return null;
                        }
                    }
                }
            } else {
                objs.add(ob);
            }
        } catch (Exception e) {
            //     System.out.println(src + " " + arg + " " + u + " " + num);
            e.printStackTrace();
            System.exit(0);
        }
        //System.out.println("Obj has "+ objs.toString());
        return objs;
    }
    // helper function
    private List<ObjectNode> sortedorder(SootMethod key) {
        List<ObjectNode> sortedmap = new ArrayList<>();
        for(ObjectNode o : existingSummaries.get(key).keySet()) {
            if(o.type == ObjectType.parameter)
                sortedmap.add(o);
        }
        for(ObjectNode o : existingSummaries.get(key).keySet()) {
            if(o.type != ObjectType.parameter)
                sortedmap.add(o);
        }
        return sortedmap;
    }
    // helper function
    public static Set<ObjectNode> getfieldObject(SootMethod src, Set<ObjectNode> obj, SootField f) {
        Set<ObjectNode> tmpobj = new HashSet<>();
        for (ObjectNode o : obj) {
            if (ptgs.get(src).fields.containsKey(o)) {
                if (ptgs.get(src).fields.get(o).containsKey(f)) {
                    tmpobj = ptgs.get(src).fields.get(o).get(f);
                }
            }
        }
        return tmpobj;
    }

    // SCC helper functions start
    /* Computes the following:
        1) Mapping of SootMethod to SCC index
        2) DAG of SCCs
    */
    private void StronglyConnectedMethods() {
        // Step 1: Generate the CallGraph
        // CallGraph cg = Scene.v().getCallGraph();

        // Step 2: Create a directed graph representation
        Map<SootMethod, List<SootMethod>> graph = new HashMap<>();
        Iterator<Edge> edges = cg.iterator();
        for(SootMethod m: solvedSummaries.keySet()){
            graph.put(m, new ArrayList<>());
        }
        while (edges.hasNext()) {
            Edge edge = edges.next();
            SootMethod src = edge.src();
            SootMethod tgt = edge.tgt();
            if (!(solvedSummaries.keySet().contains(src) & solvedSummaries.keySet().contains(tgt)))
                continue;
            //graph.computeIfAbsent(src, k -> new ArrayList<>()).add(tgt);
            graph.get(src).add(tgt);
        }
        System.out.println(graph.keySet().size());
        findSCCs(graph);
    }

    /* Implememtation of Kosaraju's Algorithm */
    private void findSCCs(Map<SootMethod, List<SootMethod>> graph) {
        Stack<SootMethod> stack = new Stack<>();
        Set<SootMethod> visited = new HashSet<>();
        
        // Step 1: Perform DFS and store finish order
        for (SootMethod method : graph.keySet()) {
            if (!visited.contains(method)) {
                dfs1(graph, method, visited, stack);
            }
        }
        
        // Step 2: Transpose the graph
        Map<SootMethod, List<SootMethod>> transposedGraph = transposeGraph(graph);
        
        // Step 3: Perform DFS on transposed graph in order of finish time
        visited.clear();
        List<ArrayList<SootMethod>> sccs = new ArrayList<>();
        int sccIndex = 0;
        
        while (!stack.isEmpty()) {
            SootMethod method = stack.pop();
            if (!visited.contains(method)) {
                ArrayList<SootMethod> scc = new ArrayList<>();
                dfs2(transposedGraph, method, visited, scc);
                for (SootMethod m : scc) {
                    methodToSccIndex.put(m, sccIndex);
                }
                sccIndexToMethod.put(sccIndex, scc);
                sccs.add(scc);
                sccIndex++;
            }
        }
        
        // Construct SCC DAG
        for (int i = 0; i < sccs.size(); i++) {
            sccDag.put(i, new HashSet<>());
        }
        for (SootMethod method : graph.keySet()) {
            int fromScc = methodToSccIndex.get(method);
            for (SootMethod neighbor : graph.getOrDefault(method, Collections.emptyList())) {
                int toScc = methodToSccIndex.get(neighbor);
                if (fromScc != toScc) {
                    sccDag.get(fromScc).add(toScc);
                }
            }
        }
    }

    private void dfs1(Map<SootMethod, List<SootMethod>> graph, SootMethod node, Set<SootMethod> visited, Stack<SootMethod> stack) {
        visited.add(node);
        for (SootMethod neighbor : graph.getOrDefault(node, Collections.emptyList())) {
            if (!visited.contains(neighbor)) {
                dfs1(graph, neighbor, visited, stack);
            }
        }
        stack.push(node);
    }

    private Map<SootMethod, List<SootMethod>> transposeGraph(Map<SootMethod, List<SootMethod>> graph) {
        Map<SootMethod, List<SootMethod>> transposed = new HashMap<>();
        for (SootMethod node : graph.keySet()) {
            for (SootMethod neighbor : graph.get(node)) {
                transposed.computeIfAbsent(neighbor, k -> new ArrayList<>()).add(node);
            }
        }
        return transposed;
    }

    private void dfs2(Map<SootMethod, List<SootMethod>> graph, SootMethod node, Set<SootMethod> visited, ArrayList<SootMethod> scc) {
        visited.add(node);
        scc.add(node);
        for (SootMethod neighbor : graph.getOrDefault(node, Collections.emptyList())) {
            if (!visited.contains(neighbor)) {
                dfs2(graph, neighbor, visited, scc);
            }
        }
    }
    /* Get the top most SCCs in the Call Graph in which the object is captured */
    private HashSet<Integer> getIndependentNodes(HashSet<Integer> nodes) {
        HashSet<Integer> independentNodes = new HashSet<>(nodes);
        for (Integer node : nodes) {
            for (Integer neighbor : sccDag.getOrDefault(node, Collections.emptySet())) {
                independentNodes.remove(neighbor);
            }
        }
        return independentNodes;
    }

    private void getInterSCCDistance() {
        int n = sccDag.size();

        // Initialize distances: 0 for same nodes, INF for others
        for (int u = 0; u < n; u++) {
            distances.put(u, new HashMap<>());
            for (int v = 0; v < n; v++) {
                distances.get(u).put(v, u == v ? 0 : Integer.MAX_VALUE);
            }
        }

        // Set direct edges with weight 1 (assuming unit weight)
        for (int u = 0; u < n; u++) {
            for (int v : sccDag.getOrDefault(u, Collections.emptySet())) {
                distances.get(u).put(v, 1);
            }
        }

        // Process nodes in topological order (0,1,2,...)
        for (int u = 0; u < n; u++) {
            for (int v : sccDag.getOrDefault(u, Collections.emptySet())) {
                for (int w = 0; w < n; w++) {
                    if (distances.get(v).get(w) != Integer.MAX_VALUE && 
                        distances.get(u).get(w) > distances.get(u).get(v) + distances.get(v).get(w)) {
                        distances.get(u).put(w, distances.get(u).get(v) + distances.get(v).get(w));
                    }
                }
            }
        }
    }
    // SCC helper functions end
    private void DownwardGlobal(){
        Set<SootMethod> keySet = existingSummaries.keySet();
        for (SootMethod m: keySet){
            if (m.isEntryMethod()){
                globalMethod=m;
            }
        }
        System.out.println("Total SCCs : "+sccIndexToMethod.size());
        for (int i=0; i<sccIndexToMethod.size(); i++){
            ArrayList<SootMethod> listofMethods = sccIndexToMethod.get(i);
            System.out.println("SCC "+i+" : "+listofMethods.size());
            for (SootMethod key: listofMethods){
                System.out.println(key.toString());
                // Check if the given method has an edge in the call graph coming from a method in another SCC
                Iterator<Edge> edgesOutOf = cg.edgesOutOf(key);
                boolean hasOutgoingEdgeToAnotherSCC = false;

                while (edgesOutOf.hasNext()) {
                    Edge edge = edgesOutOf.next();
                    SootMethod srcMethod = edge.src();
                    if (methodToSccIndex.containsKey(srcMethod) && methodToSccIndex.get(srcMethod) != methodToSccIndex.get(key)) {
                        hasOutgoingEdgeToAnotherSCC = true;
                        break;
                    }
                }

                if (hasOutgoingEdgeToAnotherSCC) {
                    List<ObjectNode> listofobjects = sortedorder(key);

                    for (ObjectNode obj: listofobjects){
                        // reason out if original_contextual_owners is even required bcz for later comparison you are
                        // using original_owners
                        //ContextualOwnershipStatus original_contextual_owners = new ContextualOwnershipStatus();
                        if (!solvedSummaries.get(key).containsKey(obj)){
                            // initialization
                            solvedSummaries.get(key).put(obj, new HashSet<>());
                        }
                        if (solvedContextualSummaries.get(key).containsKey(obj)){
                            // create deep copy of (solvedContextualSummaries.get(key).get(obj) and assign to original_contextual_owners
                        }
                        else{
                            solvedContextualSummaries.get(key).put(obj, new ContextualOwnershipStatus());
                        }
                        // add current method to solvedSummaries
                        if (key.isEntryMethod()){
                           solvedSummaries.get(key).get(obj).add(key);
                        }
                        // add current method to solvedContextualSummaries
                        Iterator<Edge> iter;
                        iter = cg.edgesInto(key);
                        while(iter.hasNext()){
                            Edge e = iter.next();
                            if (e.srcUnit()==null){
                                continue;
                            }
                            if (utils.getBCI.get(e.srcUnit()) > -1){
                                if (!solvedSummaries.keySet().contains(e.src())){
                                    continue;
                                }
                                CallSite cs = new CallSite(e.src(), utils.getBCI.get(e.srcUnit()));
                                // implement the add method in ContextualOwnershipStatus. 
                                // It should create a new key if cs already doesnt exist as a key
                                if (key.isEntryMethod()){
                                    solvedContextualSummaries.get(key).get(obj).add(cs, key);
                                }
                            }
                        }
                        EscapeStatus status = existingSummaries.get(key).get(obj);
                        for (EscapeState state : status.status){
                            if (state instanceof ConditionalValue) {
                                ConditionalValue cstate = (ConditionalValue) state;
                                if (cstate.object.type == ObjectType.parameter) {
                                    SootMethod sm = cstate.getMethod(); // the method on which this CV depends
                                    if (methodToSccIndex.get(sm) == methodToSccIndex.get(key)) {
                                        continue;
                                    }
                                    ObjectNode o = cstate.object;
                                    CallSite c = new CallSite(key, cstate.BCI);
                                    List<ObjectNode> objects = null;
                                    // reason the if condition
                                    if(cstate.fieldList != null) {
                                        iter = cg.edgesOutOf(key);
                                        while (iter.hasNext()) {
                                            Edge edge = iter.next();
                                            if(edge.getTgt().equals(sm)) {
                                                try {
                                                    // see in which scenario is this required and what does GetParmObjects do
                                                    objects = GetParmObjects(o, cstate.object.ref, sm, cstate.fieldList);
                                                } catch (Exception e) {
                                                    throw e;
                                                }
                                            }
                                        }
                                    }

                                    if(objects != null) {
                                        for(ObjectNode mappedobject : objects) {
                                            if(solvedContextualSummaries.containsKey(sm) && solvedContextualSummaries.get(sm).containsKey(mappedobject)) {
                                                ContextualOwnershipStatus cos = solvedContextualSummaries.get(sm).get(mappedobject);
                                                if(cos.ownershipMap.containsKey(c)) {
                                                    for (SootMethod temp_method: cos.ownershipMap.get(c)){
                                                        if (temp_method.isEntryMethod()){
                                                            solvedSummaries.get(key).get(obj).add(temp_method);
                                                            solvedContextualSummaries.get(key).get(obj).addForAllCs(temp_method);
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    } else {
                                        // ask the reason for this.
                                        
                                        // Seems like if cstate.fieldList is null, you simply add the methods touched by
                                        // parameter object of callee. 
                                        if(solvedContextualSummaries.containsKey(sm) && solvedContextualSummaries.get(sm).containsKey(o)) {
                                            ContextualOwnershipStatus cos = solvedContextualSummaries.get(sm).get(o);
                                            if (cos.ownershipMap.containsKey(c)) {
                                                for (SootMethod temp_method: cos.ownershipMap.get(c)){
                                                    if (temp_method.isEntryMethod()){
                                                        solvedSummaries.get(key).get(obj).add(temp_method);
                                                        solvedContextualSummaries.get(key).get(obj).addForAllCs(temp_method);
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            computeSummarySCC(i, true);
        }

    }

    // compute summaries for all methods in the call graph
    private void AddCallerSummaries(){
        Set<SootMethod> keySet = existingSummaries.keySet();
        for (SootMethod m: keySet){
            if (m.isEntryMethod()){
                globalMethod=m;
            }
        }
        System.out.println("Total SCCs : "+sccIndexToMethod.size());
        for (int i=0; i<sccIndexToMethod.size(); i++){
            ArrayList<SootMethod> listofMethods = sccIndexToMethod.get(i);
            System.out.println("SCC "+i+" : "+listofMethods.size());
            for (SootMethod key: listofMethods){
                System.out.println(key.toString());
                // Check if the given method has an edge in the call graph coming from a method in another SCC
                Iterator<Edge> edgesInto = cg.edgesInto(key);
                boolean hasIncomingEdgeFromAnotherSCC = false;

                while (edgesInto.hasNext()) {
                    Edge edge = edgesInto.next();
                    SootMethod srcMethod = edge.src();
                    if (methodToSccIndex.containsKey(srcMethod) && methodToSccIndex.get(srcMethod) != methodToSccIndex.get(key)) {
                        hasIncomingEdgeFromAnotherSCC = true;
                        break;
                    }
                }

                if (hasIncomingEdgeFromAnotherSCC) {
                    List<ObjectNode> listofobjects = sortedorder(key);

                    for (ObjectNode obj: listofobjects){
                        // reason out if original_contextual_owners is even required bcz for later comparison you are
                        // using original_owners
                        //ContextualOwnershipStatus original_contextual_owners = new ContextualOwnershipStatus();
                        if (!solvedSummaries.get(key).containsKey(obj)){
                            // initialization
                            solvedSummaries.get(key).put(obj, new HashSet<>());
                        }
                        if (solvedContextualSummaries.get(key).containsKey(obj)){
                            // create deep copy of (solvedContextualSummaries.get(key).get(obj) and assign to original_contextual_owners
                        }
                        else{
                            solvedContextualSummaries.get(key).put(obj, new ContextualOwnershipStatus());
                        }
                        // add current method to solvedSummaries
                        solvedSummaries.get(key).get(obj).add(key);
                        // add current method to solvedContextualSummaries
                        Iterator<Edge> iter;
                        iter = cg.edgesInto(key);
                        while(iter.hasNext()){
                            Edge e = iter.next();
                            if (e.srcUnit()==null){
                                continue;
                            }
                            if (utils.getBCI.get(e.srcUnit()) > -1){
                                if (!solvedSummaries.keySet().contains(e.src())){
                                    continue;
                                }
                                CallSite cs = new CallSite(e.src(), utils.getBCI.get(e.srcUnit()));
                                // implement the add method in ContextualOwnershipStatus. 
                                // It should create a new key if cs already doesnt exist as a key
                                solvedContextualSummaries.get(key).get(obj).add(cs, key);
                            }
                        }
                        EscapeStatus status = existingSummaries.get(key).get(obj);
                        for (EscapeState state : status.status){
                            if (state instanceof ConditionalValue) {
                                ConditionalValue cstate = (ConditionalValue) state;
                                if (cstate.object.type == ObjectType.returnValue) {
                                    SootMethod sm = cstate.getMethod();
                                    ObjectNode o = cstate.object;
                                    /* We have two types of return type dependencies
                                        *  1. return o1;        2. o1 = foo();
                                        *  Case 1: if the object is returned from the method;
                                        *  The method in conditional value is same as the current method in this case.
                                        */
                                    if (sm.equals(key)) {
                                        CallGraph c = Scene.v().getCallGraph();
                                        Iterator<Edge> itr = c.edgesInto(key);
                                        while(itr.hasNext()){
                                            Edge e = itr.next();
                                            if (existingSummaries.containsKey(e.src())){
                                                if (methodToSccIndex.get(e.src()) == methodToSccIndex.get(key)){
                                                    continue;
                                                }
                                                for (ObjectNode object : existingSummaries.get(e.src()).keySet()) {
                                                    Iterator<EscapeState> it = existingSummaries.get(e.src()).get(object).status.iterator();
                                                    while(it.hasNext()){
                                                        EscapeState es = it.next();
                                                        if (es instanceof ConditionalValue) {
                                                            if (((ConditionalValue) es).object.type == ObjectType.returnValue &&
                                                                    ((ConditionalValue) es).getMethod().equals(key) &&
                                                                    ((ConditionalValue) es).object.ref == cstate.object.ref) {
                                                                // think if you require ptg traversal here-->i think that must have been taken care of by static analyser
                                                                if (solvedSummaries.get(e.src()).containsKey(object)) {
                                                                    CallSite rc = new CallSite(e.src(), ((ConditionalValue) es).BCI);
                                                                    // for upward direction
                                                                    for(SootMethod temp_method: solvedSummaries.get(e.src()).get(object)){
                                                                        solvedSummaries.get(key).get(obj).add(temp_method);
                                                                        solvedContextualSummaries.get(key).get(obj).add(rc, temp_method);
                                                                        // you need to add these entries into contextual resolver too  --> done
                                                                    }
                                                                    //for downward direction
                                                                    for(SootMethod temp_method: solvedContextualSummaries.get(key).get(obj).ownershipMap.get(rc)){
                                                                        solvedSummaries.get(e.src()).get(object).add(temp_method);
                                                                        solvedContextualSummaries.get(e.src()).get(object).addForAllCs(temp_method);
                                                                        // you need to add these entries into contextual resolver too  --> done
                                                                    }
                                                                    // need to think about removing dependencies
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                                else if (cstate.object.type == ObjectType.argument){
                                    //System.out.println(key.toString()+" "+obj.toString()+" argument case");
                                    int parameternumber = cstate.object.ref;
                                    iter = cg.edgesInto(key);
                                    while (iter.hasNext()) {
                                        Edge edge = iter.next();
                                        List<ObjectNode> objects;
                                        if (!solvedSummaries.containsKey(edge.src())){
                                            continue;
                                        }
                                        if (methodToSccIndex.get(edge.src()) == methodToSccIndex.get(key)){
                                            continue;
                                        }
                                        try {
                                            objects = GetObjects(edge.srcUnit(), parameternumber, edge.src(), cstate.fieldList);
                                        } catch (Exception e) {
                                            throw e;
                                        }
                                        if (objects!=null){
                                            for (ObjectNode object: objects){
                                                if (solvedSummaries.get(edge.src()).containsKey(object)){
                                                    for (SootMethod temp_method: solvedSummaries.get(edge.src()).get(object)){
                                                        solvedSummaries.get(key).get(obj).add(temp_method);
                                                        if (utils.getBCI.get(edge.srcUnit()) > -1){
                                                            CallSite cs = new CallSite(edge.src(), utils.getBCI.get(edge.srcUnit()));
                                                            solvedContextualSummaries.get(key).get(obj).add(cs, temp_method);
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            computeSummarySCC(i, false);
        }
    }
    // compute summary for a given SCC
    void computeSummarySCC(int sccIndex, boolean downGlobal){
        ArrayList<SootMethod> listofMethods = new ArrayList<>();
        for (SootMethod temp: sccIndexToMethod.get(sccIndex)){
            listofMethods.add(temp);
        }
        Iterator<Edge> iter;
        // count number of iterations for convergence
        int counter = 0;
        // methods to add in worklist after this iteration
        HashSet<SootMethod> methodsToAdd = new HashSet<>();
        // methods to be added to worklist if a given object's solvedSummaries changes in present iteration
        HashSet<SootMethod> dependentMethods = new HashSet<>();
        HashSet<SootMethod> original_owners = new HashSet<>();
        while (!listofMethods.isEmpty()) {
            methodsToAdd.clear();
            counter++;
            //System.out.println(listofMethods.size());
            SootMethod key = listofMethods.get(0);
            listofMethods.remove(0);
            if(!existingSummaries.containsKey(key)) {
                continue;
            }
            //System.out.println(key);
            List<ObjectNode> listofobjects = sortedorder(key);
            // boolean depicting if there has been change in solvedSummaries in this iteration
            boolean flag = false;
            // boolean depicting if there has been change in solvedSummaries of a given object in this iteration
            boolean flagObject = false;

            for (ObjectNode obj: listofobjects){
                original_owners.clear();
                dependentMethods.clear();
                flagObject = false;
                // reason out if original_contextual_owners is even required bcz for later comparison you are
                // using original_owners
                //ContextualOwnershipStatus original_contextual_owners = new ContextualOwnershipStatus();
                if (solvedSummaries.get(key).containsKey(obj)){
                    for (SootMethod temp_method: solvedSummaries.get(key).get(obj)){
                        original_owners.add(temp_method);
                    }
                }
                else{
                    // initialization
                    solvedSummaries.get(key).put(obj, new HashSet<>());
                }
                if (solvedContextualSummaries.get(key).containsKey(obj)){
                    // create deep copy of (solvedContextualSummaries.get(key).get(obj) and assign to original_contextual_owners
                }
                else{
                    solvedContextualSummaries.get(key).put(obj, new ContextualOwnershipStatus());
                }
                // add current method to solvedSummaries
                solvedSummaries.get(key).get(obj).add(key);
                // add current method to solvedContextualSummaries
                iter = cg.edgesInto(key);
                while(iter.hasNext()){
                    Edge e = iter.next();
                    if (e.srcUnit()==null){
                        continue;
                    }
                    if (utils.getBCI.get(e.srcUnit()) > -1){
                        if (!solvedSummaries.keySet().contains(e.src())){
                            continue;
                        }
                        CallSite cs = new CallSite(e.src(), utils.getBCI.get(e.srcUnit()));
                        // implement the add method in ContextualOwnershipStatus. 
                        // It should create a new key if cs already doesnt exist as a key
                        solvedContextualSummaries.get(key).get(obj).add(cs, key);
                    }
                }
                EscapeStatus status = existingSummaries.get(key).get(obj);
                for (EscapeState state : status.status){
                    if (state instanceof ConditionalValue) {
                        ConditionalValue cstate = (ConditionalValue) state;
                        if (cstate.object.type == ObjectType.parameter) {
                            SootMethod sm = cstate.getMethod(); // the method on which this CV depends
                            if (methodToSccIndex.get(sm) != methodToSccIndex.get(key)) {
                                continue;
                            }
                            dependentMethods.add(sm);
                            ObjectNode o = cstate.object;
                            CallSite c = new CallSite(key, cstate.BCI);
                            List<ObjectNode> objects = null;
                            // reason the if condition
                            if(cstate.fieldList != null) {
                                iter = cg.edgesOutOf(key);
                                while (iter.hasNext()) {
                                    Edge edge = iter.next();
                                    if(edge.getTgt().equals(sm)) {
                                        try {
                                            // see in which scenario is this required and what does GetParmObjects do
                                            objects = GetParmObjects(o, cstate.object.ref, sm, cstate.fieldList);
                                        } catch (Exception e) {
                                            throw e;
                                        }
                                    }
                                }
                            }

                            if(objects != null) {
                                for(ObjectNode mappedobject : objects) {
                                    if(solvedContextualSummaries.containsKey(sm) && solvedContextualSummaries.get(sm).containsKey(mappedobject)) {
                                        ContextualOwnershipStatus cos = solvedContextualSummaries.get(sm).get(mappedobject);
                                        if(cos.ownershipMap.containsKey(c)) {
                                            for (SootMethod temp_method: cos.ownershipMap.get(c)){
                                                if (downGlobal){
                                                    if (temp_method.isEntryMethod()){
                                                        solvedSummaries.get(key).get(obj).add(temp_method);
                                                        solvedContextualSummaries.get(key).get(obj).addForAllCs(temp_method);
                                                    }
                                                }
                                                else{
                                                    solvedSummaries.get(key).get(obj).add(temp_method);
                                                    solvedContextualSummaries.get(key).get(obj).addForAllCs(temp_method);
                                                }
                                            }
                                        }
                                    }
                                }
                            } 
                            else {
                                // ask the reason for this.
                                
                                // Seems like if cstate.fieldList is null, you simply add the methods touched by
                                // parameter object of callee. 
                                if(solvedContextualSummaries.containsKey(sm) && solvedContextualSummaries.get(sm).containsKey(o)) {
                                    ContextualOwnershipStatus cos = solvedContextualSummaries.get(sm).get(o);
                                    if (cos.ownershipMap.containsKey(c)) {
                                        for (SootMethod temp_method: cos.ownershipMap.get(c)){
                                                if (downGlobal){
                                                    if (temp_method.isEntryMethod()){
                                                        solvedSummaries.get(key).get(obj).add(temp_method);
                                                        solvedContextualSummaries.get(key).get(obj).addForAllCs(temp_method);
                                                    }
                                                }
                                                else{
                                                    solvedSummaries.get(key).get(obj).add(temp_method);
                                                    solvedContextualSummaries.get(key).get(obj).addForAllCs(temp_method);
                                                }
                                        }
                                    }
                                }
                            }
                        }
                        else if (cstate.object.type == ObjectType.returnValue) {
                            SootMethod sm = cstate.getMethod();
                            ObjectNode o = cstate.object;
                            /* We have two types of return type dependencies
                                *  1. return o1;        2. o1 = foo();
                                *  Case 1: if the object is returned from the method;
                                *  The method in conditional value is same as the current method in this case.
                                */
                            if (sm.equals(key)) {
                                CallGraph c = Scene.v().getCallGraph();
                                Iterator<Edge> itr = c.edgesInto(key);
                                while(itr.hasNext()){
                                    Edge e = itr.next();
                                    if (existingSummaries.containsKey(e.src())){
                                        if (methodToSccIndex.get(e.src()) != methodToSccIndex.get(key)){
                                            continue;
                                        }
                                        dependentMethods.add(e.src());
                                        for (ObjectNode object : existingSummaries.get(e.src()).keySet()) {
                                            Iterator<EscapeState> it = existingSummaries.get(e.src()).get(object).status.iterator();
                                            while(it.hasNext()){
                                                EscapeState es = it.next();
                                                if (es instanceof ConditionalValue) {
                                                    if (((ConditionalValue) es).object.type == ObjectType.returnValue &&
                                                            ((ConditionalValue) es).getMethod().equals(key) &&
                                                            ((ConditionalValue) es).object.ref == cstate.object.ref) {
                                                        // think if you require ptg traversal here-->i think that must have been taken care of by static analyser
                                                        if (solvedSummaries.get(e.src()).containsKey(object)) {
                                                            CallSite rc = new CallSite(e.src(), ((ConditionalValue) es).BCI);
                                                            // for upward direction
                                                            for(SootMethod temp_method: solvedSummaries.get(e.src()).get(object)){
                                                                solvedSummaries.get(key).get(obj).add(temp_method);
                                                                solvedContextualSummaries.get(key).get(obj).add(rc, temp_method);
                                                                // you need to add these entries into contextual resolver too  --> done
                                                            }
                                                            //for downward direction
                                                            for(SootMethod temp_method: solvedContextualSummaries.get(key).get(obj).ownershipMap.get(rc)){
                                                                if (downGlobal){
                                                                    if (temp_method.isEntryMethod()){
                                                                        solvedSummaries.get(e.src()).get(object).add(temp_method);
                                                                        solvedContextualSummaries.get(e.src()).get(object).addForAllCs(temp_method);
                                                                    }
                                                                }
                                                                else{
                                                                    solvedSummaries.get(e.src()).get(object).add(temp_method);
                                                                    solvedContextualSummaries.get(e.src()).get(object).addForAllCs(temp_method);
                                                                }
                                                                // you need to add these entries into contextual resolver too  --> done
                                                            }
                                                            // need to think about removing dependencies
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        else if (cstate.object.type == ObjectType.global) {
                            solvedSummaries.get(key).get(obj).add(globalMethod);
                        }
                        else{
                            //System.out.println(key.toString()+" "+obj.toString()+" argument case");
                            int parameternumber = cstate.object.ref;
                            iter = cg.edgesInto(key);
                            while (iter.hasNext()) {
                                Edge edge = iter.next();
                                List<ObjectNode> objects;
                                if (!solvedSummaries.containsKey(edge.src())){
                                    continue;
                                }
                                if (methodToSccIndex.get(edge.src()) != methodToSccIndex.get(key)){
                                    continue;
                                }
                                try {
                                    objects = GetObjects(edge.srcUnit(), parameternumber, edge.src(), cstate.fieldList);
                                } catch (Exception e) {
                                    throw e;
                                }
                                if (objects!=null){
                                    dependentMethods.add(edge.src());
                                    for (ObjectNode object: objects){
                                        if (solvedSummaries.get(edge.src()).containsKey(object)){
                                            for (SootMethod temp_method: solvedSummaries.get(edge.src()).get(object)){
                                                if (downGlobal){
                                                    if (temp_method.isEntryMethod()){
                                                        solvedSummaries.get(key).get(obj).add(temp_method);
                                                        if (utils.getBCI.get(edge.srcUnit()) > -1){
                                                            CallSite cs = new CallSite(edge.src(), utils.getBCI.get(edge.srcUnit()));
                                                            solvedContextualSummaries.get(key).get(obj).add(cs, temp_method);
                                                        }
                                                    }
                                                }
                                                else{
                                                    solvedSummaries.get(key).get(obj).add(temp_method);
                                                    if (utils.getBCI.get(edge.srcUnit()) > -1){
                                                        CallSite cs = new CallSite(edge.src(), utils.getBCI.get(edge.srcUnit()));
                                                        solvedContextualSummaries.get(key).get(obj).add(cs, temp_method);
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        if (!original_owners.equals(solvedSummaries.get(key).get(obj))){
                            flagObject = true;
                            flag = true;
                        }
                    }
                }
                if (flagObject){
                    for (SootMethod m: dependentMethods){
                        methodsToAdd.add(m);
                    }
                }
            }
            if (flag){
                // iter = cg.edgesOutOf(key);
                // while (iter.hasNext()) {
                //     Edge edge = iter.next();
                //     if (!solvedSummaries.keySet().contains(edge.tgt())){
                //         continue;
                //     }
                //     listofMethods.add(edge.tgt());
                // }
                // iter = cg.edgesInto(key);
                // while (iter.hasNext()) {
                //     Edge edge = iter.next();
                //     if (!solvedSummaries.keySet().contains(edge.src())){
                //         continue;
                //     }
                //     listofMethods.add(edge.src());
                // }
                for (SootMethod m: methodsToAdd){
                    listofMethods.add(m);
                }
            }
        }
        System.out.println("Counter value: "+counter);
    }
}