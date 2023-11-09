public class Book {
    String name;
    String auther;
    int version;
    public Book(String name, String auther, int version){
        this.name = name;
        this.auther = auther;
        this.version = version;
    }

    public boolean equals(String s,int v){
        if(name.equals(s) && version==v){
            return true;
        }
        return false;
    }
}
