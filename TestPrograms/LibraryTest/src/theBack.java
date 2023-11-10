public class theBack{
    Book b = new Book("Forbidden knowledge","Xul'gurub",0);
    Book[] books = {b};
    public Book borrow(String name, int v) {
        for (Book b: books) {
            if(b.equals(name,v)){
                return b;
            }
        }
        return null;
    }
}
