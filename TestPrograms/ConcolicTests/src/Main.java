public class Main {
    public static void main(String[] args) {
        System.out.println("Hello world!");
    }

    public static int TestString(String s){
        if (s == null){
            return 0;
        } else if(s == "abc"){
            return 1;
        } else{
            if(s == null){
                return 3;
            } else {
                return 2;
            }
        }
    }

    public static int TestString2(String s){
        if (s == null){
            return 0;
        } else if(s.equals("abc")){
            return 1;
        } else{
            if(s == null){
                return 3;
            } else {
                return 2;
            }
        }
    }
}

