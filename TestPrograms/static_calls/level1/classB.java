package level1;

public class classB {
    public static void doNothing(){
        return;
    }
    public static void callC(){
        classC.doNothing();
    }
}
