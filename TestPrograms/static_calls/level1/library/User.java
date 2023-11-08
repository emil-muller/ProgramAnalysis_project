package level1.library;

public class User {
    static int capacity = 10;
    static Book[] books = new Book[capacity];
    static void borrowExample(){
        books[0] = Library.borrow("Cooking101");
        books[1] = Library.borrow("Cooking101");
        books[1] = Library.borrow("Forbidden knowledge");
    }
}
