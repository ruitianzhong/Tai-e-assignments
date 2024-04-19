public class Field {
    void bar() {
        A a = new A();
        a.x = 10;
        if (a.x == 10) {
            bar();
        }
    }
}

class A {
    public int x;
}

