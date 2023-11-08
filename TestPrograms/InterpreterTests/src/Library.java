public class Library {
    private BookEntry[] books;
    public Library(){
        books = new BookEntry[4];
        BookEntry booke = new BookEntry(1);
        booke.Name = "Book: 1";
        booke.Author = "Author: 1";
        booke.Year = 2001;
        books[0] = booke;

        BookEntry booke2 = new BookEntry(2);
        booke.Name = "Book: 2";
        booke.Author = "Author: 2";
        booke.Year = 2002;
        books[1] = booke2;

        BookEntry booke3 = new BookEntry(3);
        booke.Name = "Book: 3";
        booke.Author = "Author: 3";
        booke.Year = 2003;
        books[2] = booke3;

        BookEntry booke4 = new BookEntry(4);
        booke.Name = "Book: 4";
        booke.Author = "Author: 4";
        booke.Year = 2004;
        books[3] = booke4;
    }

    public void AddBook(String name, String author, int year, int amount, int index){
        BookEntry booke = new BookEntry(amount);
        booke.Name = "Book: " + name;
        booke.Author = "Author: " + author;
        booke.Year = year;
        books[index] = booke;
    }

    public Exception RentBook(int index){
        if(index < 0 || index > books.length){
            return ExceptionProvider.GetIndexNotFoundException();
        }

        books[index].Rent();

        return null;
    }
}
