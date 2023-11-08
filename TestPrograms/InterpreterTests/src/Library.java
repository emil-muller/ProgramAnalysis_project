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
        booke2.Name = "Book: 2";
        booke2.Author = "Author: 2";
        booke2.Year = 2002;
        books[1] = booke2;

        BookEntry booke3 = new BookEntry(3);
        booke3.Name = "Book: 3";
        booke3.Author = "Author: 3";
        booke3.Year = 2003;
        books[2] = booke3;

        BookEntry booke4 = new BookEntry(4);
        booke4.Name = "Book: 4";
        booke4.Author = "Author: 4";
        booke4.Year = 2004;
        books[3] = booke4;
    }

    public void AddBook(String name, String author, int year, int amount, int index){
        BookEntry booke = new BookEntry(amount);
        booke.Name = name;
        booke.Author =  author;
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
