public class User {
    int capacity = 10;
    Book[] books = new Book[capacity];
    Library library = new Library();

    void borrowExample(){
        books[0] = library.borrow("Cooking101",0);
        books[1] = library.borrow("Cooking101",0);
        books[1] = library.borrow("Forbidden knowledge",0);
    }

    void insertExample(){
        Book b0 = new Book("cooking103","gordan ramsay",0);
        Book b1 = new Book("cooking104","gordan ramsay",0);
        Book b2 = new Book("Coding for dummies","Ada Lovelace",0);
        library.insert(b0);
        library.insert(b1);
        library.insert(b2);
    }

    void insertManyExample(){
        for (int i = 1; i<20; i++){
            Book b0 = new Book("cooking103","gordan ramsay",0);
            library.insert(b0);
        }
    }
}
