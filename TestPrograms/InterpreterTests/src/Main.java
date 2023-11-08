public class Main {
    public static void main(String[] args) {
        System.out.println("Hello world!");
    }

    public void RentBookTest(){
        Library library = new Library();
        library.RentBook(0);
    }
    public Exception RentBookExceptionTest(){
        Library library = new Library();
        Exception e = library.RentBook(-1);
        return e;
    }
}