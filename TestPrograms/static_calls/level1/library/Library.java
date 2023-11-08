package level1.library;

import java.lang.reflect.Array;

public class Library {
    static int capacity = 10;
    static Book b0 = new Book("cooking101","gordan ramsay");
    static Book b1 = new Book("cooking102","gordan ramsay");
    static Book b2 = new Book("Coding for dummies","Ada Lovelace");
    static Book b3 = new Book("Sending messages","Alice");
    static Book b4 = new Book("Receiving messages","Bob");
    static Book[] books = {b0,b1,b2,b3,b4,null,null,null,null,null};//array of length caoacity
    static class theBack{
        static Book b = new Book("Forbidden knowledge","Xul'gurub");
        static Book[] books = {b};
        static Book borrow(String name) throws Exception{
            for (Book b: books) {
                if(b.equals(name)){
                    return b;
                }
            }
            throw new Exception("Book Is Not In The Back");
        }
    }
    static Book borrow(String name) throws Exception{
        for (Book b: books) {
            if(b.equals(name)){
                return b;
            }
        }
        return theBack.borrow(name);
    }

    static boolean insert(Book b) throws Exception{
        for (Book b2: books) {
            if(b.equals(b2.name)){
                throw new Exception("Book Already exists");
            }
        }
        for(int i = 0; i<capacity; i++){
            if (books[i]==null){
                books[i] = b;
                return true;
            }
        }
        throw new Exception("Not Enough Caoacity");
    }

    static Book[] search(){//NOT FINISHED
        return null;
    }
}
