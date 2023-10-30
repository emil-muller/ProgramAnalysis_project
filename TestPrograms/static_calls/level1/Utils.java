package level1;

public class Utils {
    public static int addnumber(int a){
        int b = getnumber();
        if (b < 10 ){
           return substruction(a,b);
        }
        return addition(a,b);
    }

    public static int getnumber(){
        return 10;
    }

    public static int addition(int a, int b){
        return a+b;
    }

    public static int substruction(int a, int b){
        return a-b;
    }
}
