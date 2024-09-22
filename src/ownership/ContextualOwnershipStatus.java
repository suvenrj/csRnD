package ownership;

import soot.SootMethod;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;

public class ContextualOwnershipStatus {
    public HashMap<CallSite, Set<SootMethod>> ownershipMap;

    public ContextualEscapeStatus(CallSite c , Set<SootMethod> methodSet) {
        ownershipMap = new HashMap<>();
        ownershipMap.put(c,methodSet);
    }
}