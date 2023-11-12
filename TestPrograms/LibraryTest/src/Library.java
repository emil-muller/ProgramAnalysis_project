public class Library {
    int capacity = 10;
    Book b0 = new Book("cooking101","gordan ramsay",0);
    Book b1 = new Book("cooking102","gordan ramsay",0);
    Book b2 = new Book("Coding for dummies","Ada Lovelace",0);
    Book b3 = new Book("Sending messages","Alice",0);
    Book b4 = new Book("Receiving messages","Bob",0);
    Book[] books = {b0,b1,b2,b3,b4,null,null,null,null,null};//array of length capacity
    theBack back = new theBack();

    Book borrow(String name, int v) {
        for (Book b: books) {
            if(b.equals(name,v)){
                return b;
            }
        }
        return back.borrow(name,v);
    }

    boolean insert(Book b) {
        for (Book b2: books) {
            if(b.equals(b2.name, b2.version)){
                return false;
            }
        }
        for(int i = 0; i<capacity; i++){
            if (books[i]==null){
                books[i] = b;
                return true;
            }
        }
        return false;
    }

    Book[] search(){//NOT FINISHED
        return null;
    }
}
