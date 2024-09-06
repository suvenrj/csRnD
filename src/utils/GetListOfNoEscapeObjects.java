package utils;

import es.EscapeStatus;
import ptg.ObjectNode;
import ptg.ObjectType;

import java.util.ArrayList;
import java.util.HashMap;

public class GetListOfNoEscapeObjects {
	public static String get(
			HashMap<ObjectNode, EscapeStatus> summary,
			ArrayList<ObjectNode> stackOrder) {
		ArrayList<Integer> arr = new ArrayList<>();
		for (ObjectNode obj : stackOrder) {
			if (obj.type != ObjectType.internal)
				continue;
			EscapeStatus es = summary.get(obj);
			if (es.containsNoEscape())
				arr.add(obj.ref);
		}

		if (arr.size() > 0) {
			String _ret = arr.toString();
			return _ret;
		} else {
			return null;
		}
	}
}
