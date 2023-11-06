public class Main {
    public static void main(String[] args) {
        System.out.println("Hello world!");
    }

    public void CallsInheritedVoidMethod(){
        BExtendsA B = new BExtendsA();
        B.VoidA();
    }

    public void CallsInheritedIntMethod(){
        BExtendsA B = new BExtendsA();
        B.ReturnA();
    }

    public int GetsInheritedProperty(){
        BExtendsA B = new BExtendsA();
        return B.A;
    }

    public void CallsInterfaceMethodWithoutInterface(){
        ImplementsIA C = new ImplementsIA();
        C.InterfaceVoid();
    }

    public int CallsInterfaceMethodWithInterface(){
        ImplementsIA C = new ImplementsIA();
        IA ia = C;
        return ia.InterfaceInt();
    }
}