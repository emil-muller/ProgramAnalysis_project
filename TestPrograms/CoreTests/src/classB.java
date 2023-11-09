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
}
