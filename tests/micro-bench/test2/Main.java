// Check handling of inlining case
import java.lang.*;
public class Main {
	public static Node A;
//	static {
//		A =  new Node();
//	}
	public static void main(String[] args) {
		A a = new A();
		B b = new B();
		a.foo(b);
	}
}

class A {
	A glbl;
	A f1;
	void foo(B p) {
		C c = new C(); // c = <>
		A x = this.fb(p);
		A y = x.bar(); // y = <external, 18>
		if(y instanceof B)
			System.out.println("B");
		else
			System.out.println("C");
		A z = c.fb(y);
		//foobar();
		// glbl = new A();
		// glbl.f1 = z;
		if(z instanceof B)
			System.out.println("B");
		else
			System.out.println("C");
	}

	A fb(A p) {
		if(p instanceof B) {
			return new B();
		}
		else return new C();
	}

	A bar() {
		return new A();
	}

//	void foobar() {
//		C x  = new C();
//		A y  = new C();
//		y = x.bar();
//	}

}

class B extends A {
	A bar() {
		return new B();
	}
}

class C extends A {
	A bar() {
		return new C();
	}
}
