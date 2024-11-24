public class Main {

	static Node g;
	public static void main(String[] args) {
		Node A = new Node();
		Node B = new Node();
		Node C = new Node();
		Node D = new Node();
		func(A, C, D);
	}

	public static void func(Node p1, Node p2, Node p3) {
		func2(p1, p2);
	}
	public static void func2(Node p1, Node p2){
	}
}
