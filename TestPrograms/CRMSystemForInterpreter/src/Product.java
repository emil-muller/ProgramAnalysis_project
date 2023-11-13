public class Product {
    private String name;
    private double price;

    public Product(String newName, double newPrice) {
        name = newName;
        price = newPrice;
    }

    public String getName() {
        return name;
    }

    public double getPrice() {
        return price;
    }
}