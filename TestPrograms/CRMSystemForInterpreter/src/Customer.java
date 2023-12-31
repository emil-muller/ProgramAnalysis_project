/**
 * This code was generated by Chat-GPT and the final
 * version was copied and slightly modified in order
 * to suit our test needs. The prompts and used with
 * Chat-GPT can be found below:
 * https://chat.openai.com/share/9da8643e-4878-4a84-b587-82d2543b9735
 *
 * This is also covered in more detail in our report.
 */
public class Customer extends Person {
    private boolean isVIP;

    public Customer(String newName, String newEmail, boolean newIsVIP) {
        super(newName, newEmail);
        isVIP = newIsVIP;
    }

    public void displayInfo() {
        //System.out.println("Customer Name: " + name + ", Email: " + email + ", VIP: " + isVIP);
    }

    public boolean isVIP() {
        return isVIP;
    }
}