package ownership;

import soot.SootMethod;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;

import es.CallSite;

public class ContextualOwnershipStatus {
    public HashMap<CallSite, HashSet<SootMethod>> ownershipMap;

    public ContextualOwnershipStatus(){
        ownershipMap = new HashMap<>();
    }

    public ContextualOwnershipStatus(CallSite c , HashSet<SootMethod> methodSet) {
        ownershipMap = new HashMap<>();
        ownershipMap.put(c,methodSet);
    }

    public void add(CallSite c, SootMethod m){
        boolean flag = false;
        for (CallSite cs: ownershipMap.keySet()){
            if (cs.equals(c)){
                ownershipMap.get(cs).add(m);
                flag = true;
                break;
            }
        }
        if (!flag){
            ownershipMap.put(c , new HashSet<>());
            ownershipMap.get(c).add(m);
        }
    }
    
    public void addForAllCs(SootMethod m){
        for (CallSite cs: ownershipMap.keySet()){
            ownershipMap.get(cs).add(m);
        }
    }
}