public class CharArgs {

    static char foo(char x, char y) {
        return (char) (x + y);
    }


    public static void main(String[] args) {
        char x = 1;
        char y = 2;
        char z = foo(x, y);
        int temp = new A().Ten();
    }
}

class A {

    public int x;

    int Ten() {
        return this.x;
    }
}