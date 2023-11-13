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