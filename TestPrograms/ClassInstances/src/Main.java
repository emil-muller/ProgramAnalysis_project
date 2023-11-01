public class Main {
    public static void main(String[] args) {
    }

    public void CreateClassInstance(){
        SimpleClass simple = new SimpleClass();
    }
    public int CreateClassInstanceParameter(int x){
        SimpleClass simple = new SimpleClass(x);
        return simple.PublicProperty;
    }

    public int AccessStaticProperty(){
        return SimpleClass.StaticProperty;
    }

    public int InvokeMethod(){
        SimpleClass simple = new SimpleClass();
        return simple.ReturnMember();
    }
}