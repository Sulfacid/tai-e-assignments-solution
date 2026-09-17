class MyTest {
    int test() {
        int x = 0;
        int y = 2;
        int z = 0;
        int i = 1;
        switch(x + y) {
            case 0:
                i = z;
                break;
            case 1:
                z = 3;
                break;
            default:
                z = i;
        }
        return i;
    }
}