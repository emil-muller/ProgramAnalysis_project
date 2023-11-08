package level1.library;

public class User {
    static int capacity = 10;
    static Book[] books = new Book[capacity];
    static void borrowExample(){
        try{
            books[0] = Library.borrow("Cooking101");
            books[1] = Library.borrow("Cooking101");
            books[1] = Library.borrow("Forbidden knowledge");
        }catch (Exception e){
            //Welp
        }
    }

    static void insertExample(){
        try{
            Book b0 = new Book("cooking103","gordan ramsay");
            Book b1 = new Book("cooking104","gordan ramsay");
            Book b2 = new Book("Coding for dummies","Ada Lovelace");
        }catch (Exception e){
            //Welp
        }
    }

    static void insertManyExample(){
        try{
            for (int i = 1; i<20; i++){
                Book b0 = new Book("cooking103","gordan ramsay");
                Library.insert(b0);
            }
        }catch (Exception e){
            //Welp
        }
    }
}
