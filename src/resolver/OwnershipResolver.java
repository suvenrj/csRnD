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

public class OwnershipResolver {
    // need to evaluate private/public for these Data structures
    public static Map<SootMethod,HashMap<ObjectNode, EscapeStatus>> existingSummaries; // from static analyser
    private static Map<SootMethod,PointsToGraph> ptgs; // to store method ptgs
    public static Map<SootMethod,HashMap<ObjectNode, Set<SootMethod>>> solvedSummaries; // non contextual ownership list
    public static Map<SootMethod,HashMap<ObjectNode, List<ContextualOwnershipStatus>>> solvedContextualSummaries; // 1-level contextual ownership list
    List<SootMethod> noBCIMethods; // methods from where we need to consider an object escaping

    public OwnershipResolver(Map<SootMethod, HashMap<ObjectNode, EscapeStatus>> existingSummaries, Map<SootMethod, PointsToGraph> ptgs, List<SootMethod> escapingMethods){
        // initialization of data structures
        ContextualResolver.existingSummaries = existingSummaries;
        ContextualResolver.ptgs = ptgs;
        this.noBCIMethods = escapingMethods;
        solvedContextualSummaries = new HashMap<>();
        solvedSummaries = new HashMap<>();

        for (Map.Entry<SootMethod, HashMap<ObjectNode, EscapeStatus>> entry : existingSummaries.entrySet()) {
            SootMethod method = entry.getKey();
            solvedContextualSummaries.put(method, new HashMap<>());
            solvedSummaries.put(method, new HashMap<>());
        }

        AddCallerSummaries();

    }
    // function to resolve
    void AddCallerSummaries(){
        CallGraph cg = Scene.v().getCallGraph();
        ArrayList<SootMethod> listofMethods = new ArrayList<>(existingSummaries.keySet());
        while (!listofMethods.isEmpty()) {
            for (SootMethod key : listofMethods) {
                // why have this if condition
                if(!existingSummaries.containsKey(key)) {
                    continue;
                }
                List<ObjectNode> listofobjects = sortedorder(key);
                for (ObjectNode obj: listofobjects){
                    Set<SootMethod> original_owners = new Set<>();
                    for (SootMethod temp_method: solvedSummaries.get(key).get(obj)){
                        original_owners.add(temp_method);
                    }
                    EscapeStatus status = existingSummaries.get(key).get(obj);
                    solvedSummaries.get(key).get(obj).add(key);
                    for (EscapeState state : status.status){
                        if (state instanceof ConditionalValue) {
                            ConditionalValue cstate = (ConditionalValue) state;
                            if (cstate.object.type == ObjectType.parameter) {
                                SootMethod sm = cstate.getMethod(); // the method on which this CV depends
                                ObjectNode o = cstate.object;
                                CallSite c = new CallSite(key, cstate.BCI);
                                List<ObjectNode> objects = null;
                                
                                if(cstate.fieldList != null) {
                                    Iterator<Edge> iter = cg.edgesOutOf(key);
                                    while (iter.hasNext()) {
                                        Edge edge = iter.next();
                                        if(edge.getTgt().equals(sm)) {
                                            try {
                                                objects = GetParmObjects(o, cstate.object.ref, sm, cstate.fieldList);
                                            } catch (Exception e) {
                                                throw e;
                                            }
                                        }
                                    }
                                }

                                if(objects != null) {
                                    for( ObjectNode mappedobject : objects) {
                                        if(solvedContextualSummaries.containsKey(sm) && solvedContextualSummaries.get(sm).containsKey(mappedobject)) {
                                            for(ContextualOwnershipStatus cos : solvedContextualSummaries.get(sm).get(mappedobject)) {
                                                if(cos.ownershipMap.containsKey(c)) {
                                                    for (SootMethod temp_method: cos.ownershipMap.getKey(c)){
                                                        solvedSummaries.get(key).get(obj).add(temp_method);
                                                    }
                                                }
                                            }
                                        }
                                    }
                                } else {
                                    // ask the reason for this
                                    if(solvedContextualSummaries.containsKey(sm) && solvedContextualSummaries.get(sm).containsKey(o)) {
                                        for(ContextualOwnershipStatus cos : solvedContextualSummaries.get(sm).get(o)) {
                                            if (cos.ownershipMap.containsKey(c)) {
                                                for (SootMethod temp_method: cos.ownershipMap.getKey(c)){
                                                    solvedSummaries.get(key).get(obj).add(temp_method);
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
                                    *  First directly mark the Object as escaping
                                    */
                                if (sm.equals(key)) {
                                    CallGraph c = Scene.v().getCallGraph();
                                    Iterator<Edge> itr = c.edgesInto(key);
                                    while(itr.hasNext()){
                                        Edge e = itr.next();
                                        for (ObjectNode object : existingSummaries.get(e.src()).keySet()) {
                                            Iterator<EscapeState> it = existingSummaries.get(e.src()).get(object).status.iterator();
                                            while(it.hasNext()){
                                                EscapeState es = it.next();
                                                if (es instanceof ConditionalValue) {
                                                    if (((ConditionalValue) es).object.type == ObjectType.returnValue &&
                                                            ((ConditionalValue) es).getMethod().equals(key) &&
                                                            ((ConditionalValue) es).object.ref == cstate.object.ref) {
                                                        // think if you require ptg traversal here
                                                        if (solvedSummaries.get(e.src()).containsKey(object)) {
                                                            // for upward direction
                                                            for(SootMethod temp_method: solvedSummaries.get(e.src()).get(object)){
                                                                solvedSummaries.get(key).get(obj).add(temp_method);
                                                                // you need to add these entries into contextual resolver too
                                                            }
                                                            //for downward direction
                                                            for(SootMethod temp_method: solvedSummaries.get(key).get(obj)){
                                                                solvedSummaries.get(e.src()).get(object).add(temp_method);
                                                                // you need to add these entries into contextual resolver too
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
                            else if (cstate.object.type == ObjectType.global) {
                            }
                            else{
                                int parameternumber = cstate.object.ref;
                                Iterator<Edge> iter = cg.edgesInto(key);
                                while (iter.hasNext()) {
                                    Edge edge = iter.next();
                                    List<ObjectNode> objects;
                                    try {
                                        objects = GetObjects(edge.srcUnit(), parameternumber, edge.src(), cstate.fieldList);
                                    } catch (Exception e) {
                                        throw e;
                                    }

                                    for (ObjectNode object: objects){
                                        for (SootMethod temp_method: solvedSummaries.get(edge.src()).get(object)){
                                            solvedSummaries.get(key).get(obj).add(temp_method);
                                            // fill solvedcontextualsummaries here as well
                                        }
                                    }
                                }
                            }
                            if (original_owners != solvedSummaries.get(key).get(obj)){
                                // all dependent methods need to be added to worklist
                            }
                            // remove current method from worklist
                        }
                    }
                }
            }
        }
    }
}
