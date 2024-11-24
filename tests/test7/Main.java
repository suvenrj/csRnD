public class Main {
	public static void main(String[] args) {
		test();
	}

	public static void test() {
		Node A = new Node();
		Node B = new Node();
		Node C = new Node();
		Node D = new Node();
		A.n = C;
		GlobalVars.n1 = A;
		GlobalVars.n2 = B;
	}
}
