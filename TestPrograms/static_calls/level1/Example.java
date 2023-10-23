package level1;

import level1.*;

public class Example {
    public static void main(String[] args) {
        int a = 5;
        int out = Utils.addnumber(a);
        Other.PrintSomething(out);
        Other.PrintSomething(Other.doRandomStuff());
    }
}
