package level1.library;

public class Book {
    String name;
    String auther;

    public Book(String name, String auther){
        this.name = name;
        this.auther = auther;
    }

    public boolean equals(String s){
        if(name.equals(s)){
            return true;
        }
        return false;
    }
}
