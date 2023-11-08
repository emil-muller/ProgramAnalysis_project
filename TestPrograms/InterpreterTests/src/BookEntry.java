public class BookEntry extends Book {
    public int InStore;
    private int rented;

    public BookEntry(int amount){
        InStore = amount;
    }

    public boolean AnyAvailable(){
        return (InStore - rented) > 0;
    }

    public void Rent(){
        rented += 1;
    }
}
