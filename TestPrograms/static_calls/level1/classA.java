package level1;

public class classA {
    public static void test1(int x){
        if(x>10){
            classB.callC();
        }else{
            classB.doNothing();
        }
        classB.doNothing();
    }
    public static void doNothing(){
        return;
    }
}
