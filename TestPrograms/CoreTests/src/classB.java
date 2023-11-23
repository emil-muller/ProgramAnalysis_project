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

    public static boolean isTrue(boolean b){
        return b;
    }

    public classB(){}

    public void instanceDoNothing(){}

    public void instanceCallC(classC c){
        c.instanceDoNothing();
    }

    public static void redundantBranching(int x){
        if(x<10){
            classC.doNothing();
        }else{
            classB.doNothing();
        }
    }

    public static void testtest(){
        classC.testtest();
    }

    public static void testtest2(){

    }

    public static classC getC(){
        return new classC();
    }

    public classB getBI(){
        return new classB();
    }

    public classC getCI(){
        return new classC();
    }
}
