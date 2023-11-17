public class classA {
    public static void recursionSimple(boolean recursive){
        if(recursive){
            classB.callARecursionSimple();
        }
    }

    public static void recursion(int x){
        if(x>0){
            classB.callARecursion(x);
        }
    }

    public static void backAndForth(){
        classB.callA();
    }


    public static void nonOverlappingAlternatives(int x){
        if(x>10){
            classB.doNothing();
        }
        if(x==10){
            classB.doNothing();
        }
        if(x<10){
            classB.doNothing();
        }
    }

    public static void clearlyImpossibleCase(int x){
        classB.doNothing();
        if(false){
            classC.doNothing();
        }
    }

    public static void impossibleCases(int x){
        x = 10;
        if(x>10){
            classB.doNothing();
        }
        if(x==10){
            classB.doNothing();
        }
        if(x<10){
            classB.doNothing();
        }
    }

    public static void nestedIf(int x){
        if(x>3){
            if(x>2){
                if(x>1){
                    classB.doNothing();
                }
            }
        }
        classC.doNothing();
    }

    public static void indirectImpossibleCase(int x){
        x = 10;
        if(x==10){
            classB.testX(x);
        }
    }

    public static void indirectNestedCase(int x){
        if(x<10){
            classB.testX(x);
        }
    }

    public static void overTheTop(int x){
        if(x>10){
            classB.overTheTopB(x);
        }
        if(x==10){
            classB.overTheTopB(x);
        }
        if(x<10){
            classB.overTheTopB(x);
        }
    }


    public static void doNothing(){
        return;
    }

    public static void simpleloopTest(){
        for(int i = 0; i<10; i++){
            classB.doNothing();
        }
    }

    public static void simpleloopTest2(){
        for(int i = 0; i<10; i++){
            classB.doNothing();
            classC.doNothing();
        }
    }

    public static void loopTest(){
        for(int i = 0; i<10; i++){
            classB.loopTest(i);
        }
    }

    public static void compressTest(){
        classB.doNothing();
        classB.doNothing();
        classB.doNothing();
        classB.doNothing();
        classB.doNothing();
        classB.doNothing();
        classB.doNothing();
        classB.doNothing();
        classB.doNothing();
        classB.doNothing();
    }

    public static void compressTest2(){
        classB.doNothing();
        classC.doNothing();
        classB.doNothing();
        classC.doNothing();
        classB.doNothing();
        classC.doNothing();
        classB.doNothing();
        classC.doNothing();
        classB.doNothing();
        classC.doNothing();
    }

    public static void instanceExample(){
        classB b1 = new classB();
        classB b2 = new classB();
        b1.instanceDoNothing();
        b1.instanceDoNothing();
        b2.instanceDoNothing();
    }

    public static void instanceToInstanceExample(){
        classB b1 = new classB();
        classB b2 = new classB();
        classC c1 = new classC();
        classC c2 = new classC();
        b1.instanceCallC(c1);
        b2.instanceCallC(c1);
        c2.instanceDoNothing();
    }

    public static void methodInIf(){
        classB.doNothing();
        if (classB.isTrue(true)){
            classC.doNothing();
        }
    }

    public static void redundantBranching(int x){
        if(x<10){
            classB.redundantBranching(x);
        }else{
            classC.doNothing();
        }
    }

    public static void unnecessaryBranching(int x){
        if(x<10){
            classB.doNothing();
        }else{
            classB.doNothing();
        }
    }
}
