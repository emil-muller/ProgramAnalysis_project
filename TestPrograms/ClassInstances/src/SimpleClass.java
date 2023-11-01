public class SimpleClass {
    public int PublicProperty = 1;
    private int PrivateProperty = 2;
    public static int StaticProperty = 3;

    public static void StaticMethod(){
        return;
    }

    public void VoidMethod(){
        return;
    }

    public int ReturnMember(){
        return PrivateProperty;
    }
}
