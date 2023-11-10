public class classB {
    public static void doNothing(){
        return;
    }

    public static void testX(int x){
        if(x<10){
            classC.doNothing();
        }
    }

    public static void overTheTopB(int x){
        if(x>10){
            classC.doNothing();
        }
        if(x==10){
            classC.doNothing();
        }
        if(x<10){
            classC.doNothing();
        }
    }

    public static void callC(){
        classC.doNothing();
    }

    public static void callA(){
        classA.doNothing();
    }

    public static void callARecursion(int x){
        classA.recursion(x-1);
    }

    public static void callARecursionSimple(){
        classA.recursionSimple(false);
    }

    public static void loopTest(int i){
        if(i<4){
            classC.doNothing();
        }
    }
}
