public class Main {
	public static void main(String[] args) {
		Node A = new Node();
		Node B = new Node();
		Node C = new Node();
		Node D = new Node();
		func(A, C, D);
	}

	public static void func(Node p1, Node p2, Node p3) {
		p1.n = p3;
		func2(p1, p2);
	}
	public static void func2(Node p1, Node p2) {
		p1.n = p2;
		Node a = new Node();
		Node b = new Node();
		Node c = new Node();
		func(a, b, c);
	}

	// public static void func3(Node p1){
	// 	p1 = new Node();
	// 	func2(p1, p1);
	// }
}
