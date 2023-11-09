public class theBack{
    static Book b = new Book("Forbidden knowledge","Xul'gurub",0);
    static Book[] books = {b};
    static Book borrow(String name, int v) {
        for (Book b: books) {
            if(b.equals(name,v)){
                return b;
            }
        }
        return null;
    }
}
