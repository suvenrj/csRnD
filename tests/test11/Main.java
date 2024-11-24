public class Main {
	public static void main(String[] args) {
		Node A = new Node();
		Node B = new Node();
		// Node C = new Node();
		// Node D = new Node();
		func(A);
		func2(A,B);
	}

	public static void func(Node p1) {
		Node a = new Node();
		func3(a);
		GlobalVars.n1 = a;
	}

	public static void func2(Node p1, Node p2){
		Node b = new Node();
		func3(b);
	}

	public static void func3(Node p1){
		func4(p1);
	}

	public static void func4(Node p1){
		p1.n = new Node();
	}
}
