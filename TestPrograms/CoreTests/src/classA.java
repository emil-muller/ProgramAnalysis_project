public class classA {

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
        if(false){
            classB.doNothing();
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
}
