/**
 * This code was generated by Chat-GPT and the final
 * version was copied and slightly modified in order
 * to suit our test needs. The prompts and used with
 * Chat-GPT can be found below:
 * https://chat.openai.com/share/9da8643e-4878-4a84-b587-82d2543b9735
 *
 * This is also covered in more detail in our report.
 */
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