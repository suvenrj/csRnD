public class Main {
	public static void main(String[] args) {
		Node A = new Node();
		Node B = new Node();
		Node C = new Node();
		Node D = new Node();
		Node a = func();
		a.n.n = new Node();
	}

	public static Node func() {
		Node a = new Node();
		a.n = new Node();
		return a;
	}
}
