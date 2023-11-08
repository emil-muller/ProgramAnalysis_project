public class Library {
    private BookEntry[] books;
    public Library(){
        int amount = 100;
        books = new BookEntry[amount];
        for(int i = 0; i < amount; i++){
            BookEntry booke = new BookEntry(i);
            booke.Name = "Book: " + i;
            booke.Author = "Author: " + i;
            booke.Year = 2000 + i;
            books[i] = booke;
        }
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
