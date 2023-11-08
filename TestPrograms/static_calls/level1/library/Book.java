package level1.library;

public class Book {
    String name;
    String auther;
    int version;
    public Book(String name, String auther){
        this.name = name;
        this.auther = auther;
        version = 0;
    }

    public Book(String name, String auther, int version){
        this.name = name;
        this.auther = auther;
        this.version = version;
    }

    public boolean equals(String s){
        if(name.equals(s) && version==version){
            return true;
        }
        return false;
    }
}
