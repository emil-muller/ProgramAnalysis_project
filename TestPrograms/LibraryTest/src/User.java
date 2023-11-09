public class User {
    static int capacity = 10;
    static Book[] books = new Book[capacity];
    static void borrowExample(){
        books[0] = Library.borrow("Cooking101",0);
        books[1] = Library.borrow("Cooking101",0);
        books[1] = Library.borrow("Forbidden knowledge",0);
    }

    static void insertExample(){
        Book b0 = new Book("cooking103","gordan ramsay",0);
        Book b1 = new Book("cooking104","gordan ramsay",0);
        Book b2 = new Book("Coding for dummies","Ada Lovelace",0);
        Library.insert(b0);
        Library.insert(b1);
        Library.insert(b2);
    }

    static void insertManyExample(){
        for (int i = 1; i<20; i++){
            Book b0 = new Book("cooking103","gordan ramsay",0);
            Library.insert(b0);
        }
    }
}
