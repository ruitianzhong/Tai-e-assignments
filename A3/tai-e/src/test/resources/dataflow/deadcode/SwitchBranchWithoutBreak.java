class SwitchBranchWithoutBreak {
    void switchFunc() {
        int x = 2, y;
        switch (x) {
            case 1:
                use();
                break; // unreachable branch
            case 2:
                use();
            case 3:
                use();
                break; // fall through
            default:
                use(); // unreachable branch
        }
    }

    void use() {
        int a = 1, b = 2;
        while (a == 1) {
            if (b > 2) {
                temp();
            }
            a = -1;
            while (a < 0) {
                temp();
            }
        }
    }

    void temp() {

    }

}