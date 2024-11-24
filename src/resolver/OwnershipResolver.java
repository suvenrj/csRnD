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
    public static HashMap<SootMethod,HashMap<ObjectNode, HashSet<SootMethod>>> solvedSummaries; // non contextual ownership list
    public static HashMap<SootMethod,HashMap<ObjectNode, ContextualOwnershipStatus>> solvedContextualSummaries; // 1-level contextual ownership list
    List<SootMethod> noBCIMethods; // methods from where we need to consider an object escaping

    public OwnershipResolver(Map<SootMethod, HashMap<ObjectNode, EscapeStatus>> existingSummaries, Map<SootMethod, PointsToGraph> ptgs, List<SootMethod> escapingMethods){
        // initialization of data structures
        OwnershipResolver.existingSummaries = existingSummaries;
        OwnershipResolver.ptgs = ptgs;
        this.noBCIMethods = escapingMethods;
        solvedContextualSummaries = new HashMap<>();
        solvedSummaries = new HashMap<>();

        for (Map.Entry<SootMethod, HashMap<ObjectNode, EscapeStatus>> entry : existingSummaries.entrySet()) {
            SootMethod method = entry.getKey();
            solvedContextualSummaries.put(method, new HashMap<>());
            solvedSummaries.put(method, new HashMap<>());
        }

        AddCallerSummaries();

        for (SootMethod key: solvedSummaries.keySet()){
            for (ObjectNode obj: solvedSummaries.get(key).keySet()){
                System.out.println(key.toString()+" "+obj.toString());
                for (SootMethod m: solvedSummaries.get(key).get(obj)){
                    System.out.println(m);
                }
            }
        }
        System.out.println("Suven");
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
    public static List<ObjectNode> GetObjects(Unit u, int num, SootMethod src, List<SootField> fieldList) {
        List<ObjectNode> objs = new ArrayList<>();
        InvokeExpr expr;
        if (u instanceof JInvokeStmt) {
            expr = ((JInvokeStmt) u).getInvokeExpr();
//            System.out.println("1"+ expr.toString());
        } else if (u instanceof JAssignStmt) {
            expr = (InvokeExpr) (((JAssignStmt) u).getRightOp());
//            System.out.println("2"+ expr.toString());
        } else {
//            System.out.println("3"+ u.toString());
            return null;
        }
        Value arg = null;
        try {
            if (num >= 0) {
                //System.out.println("Num : "+ num + " expr is : "+ expr.toString());
                if(expr.getArgCount() > num)
                    arg = expr.getArg(num);
            } else if (num == -1 && (expr instanceof AbstractInstanceInvokeExpr)) {
                arg = ((AbstractInstanceInvokeExpr) expr).getBase();
                //System.out.println("For -1 : expr is "+ expr + "arg value is : "+ arg.toString());
            }
            else return null;

        } catch (Exception e) {
            System.err.println(u + " " + num + " " + expr);
            CallGraph cg = Scene.v().getCallGraph();
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
//            System.out.println("Reaching here with source: "+ src.toString() + "and arg : "+ arg);
            if(ptgs.containsKey(src)) {
                if (ptgs.get(src).vars.containsKey(arg)) {
//                    System.out.println("Reached Inside");
                    for (ObjectNode o : ptgs.get(src).vars.get(arg)) {
//                        System.out.println("Object is : "+ o.toString());
                        if (fieldList != null) {
//                            System.out.println("Reaching inside as field list is : "+ fieldList.toString());
                            Set<ObjectNode> obj = new HashSet<>();
                            Set<ObjectNode> obj1 = new HashSet<>();
                            obj1.add(o);
                            for (SootField f : fieldList) {
//                                System.out.println("Field is "+ f.toString());
                                obj = getfieldObject(src, obj1, f);
                                if (obj.isEmpty()) {
                                    //objs.add(o);
                                    return null;
                                }
//                                System.out.println("Obj is "+ obj.toString());
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
//            System.out.println(src + " " + arg + " " + u + " " + num);
            e.printStackTrace();
            System.exit(0);
        }
        //System.out.println("Obj has "+ objs.toString());
        return objs;
    }
    //helper functions
    public static List<ObjectNode> GetParmObjects(ObjectNode ob, int num, SootMethod tgt, List<SootField> fieldList) {
        List<ObjectNode> objs = new ArrayList<>();
        try {
//          System.out.println("Reaching here with source: "+ tgt.toString() + "and fieldlist : "+ fieldList);
            if (fieldList != null) {
                if(ptgs.containsKey(tgt)) {
                    if (ptgs.get(tgt).fields.containsKey(ob)) {
//                        System.out.println("Reached Inside");
                        Set<ObjectNode> obj = new HashSet<>();
                        Set<ObjectNode> obj1 = new HashSet<>();
                        obj1.add(ob);
                        for (SootField f : fieldList) {
//                          System.out.println("Object is : "+ ob.toString());
//                          System.out.println("Reaching inside as field list is : "+ fieldList.toString());
//                          System.out.println("Field is "+ f.toString());
                            obj = getfieldObject(tgt, obj1, f);
                            if (obj.isEmpty()) {
                                //objs.add(o);
                                return null;
                            }
//                        System.out.println("Obj is "+ obj.toString());
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
    // function to resolve
    void AddCallerSummaries(){
        CallGraph cg = Scene.v().getCallGraph();
        Set<SootMethod> keySet = existingSummaries.keySet();
        SootMethod globalMethod=null;
        for (SootMethod m: keySet){
            if (m.isEntryMethod()){
                globalMethod=m;
                System.out.println("Entry point is: "+globalMethod.toString());
            }
        }
        Queue<SootMethod> listofMethods = new LinkedList<>(keySet);
        Iterator<Edge> iter;
        while (!listofMethods.isEmpty()) {
            // get head of worklist
            SootMethod key = listofMethods.remove();
            if(!existingSummaries.containsKey(key)) {
                continue;
            }
            //System.out.println(key);
            List<ObjectNode> listofobjects = sortedorder(key);
            // boolean depicting if there has been change in solvedSummaries in this iteration
            boolean flag = false;
            for (ObjectNode obj: listofobjects){
                HashSet<SootMethod> original_owners = new HashSet<>();
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
                    if (utils.getBCI.get(e.srcUnit()) > -1){
                        if (e.src().isJavaLibraryMethod()){
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
                                                solvedSummaries.get(key).get(obj).add(temp_method);
                                                solvedContextualSummaries.get(key).get(obj).addForAllCs(temp_method);
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
                                            solvedSummaries.get(key).get(obj).add(temp_method);
                                            solvedContextualSummaries.get(key).get(obj).addForAllCs(temp_method);
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
                        if (!original_owners.equals(solvedSummaries.get(key).get(obj))){
                            flag = true;
                        }
                    }
                }
                // System.out.println(key.toString()+" "+obj.toString());
                // for (SootMethod t: solvedSummaries.get(key).get(obj)){
                //     System.out.println(t);
                // }
            }
            if (flag){
                iter = cg.edgesOutOf(key);
                while (iter.hasNext()) {
                    Edge edge = iter.next();
                    if (edge.tgt().isJavaLibraryMethod() || edge.tgt().toString().startsWith("<openj9") || edge.tgt().toString().contains("init")){
                        continue;
                    }
                    listofMethods.add(edge.tgt());
                }
                iter = cg.edgesInto(key);
                while (iter.hasNext()) {
                    Edge edge = iter.next();
                    // if (edge.src().isJavaLibraryMethod()){
                    //     continue;
                    // }
                    listofMethods.add(edge.src());
                }
            }
        }
    }
}
