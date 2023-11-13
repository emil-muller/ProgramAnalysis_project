public class Sale {
    private Customer customer;
    private Product product;
    private int quantity;
    private double totalAmount;
    private boolean saleProcessed;

    public Sale(Customer newCustomer, Product newProduct, int newQuantity) {
        customer = newCustomer;
        product = newProduct;
        quantity = newQuantity;
        totalAmount = 0.0;
        saleProcessed = false;
    }

    public void processSale() {
        if (!saleProcessed) {
            if (product != null && quantity > 0) {
                double productPrice = product.getPrice();
                totalAmount = productPrice * quantity;
                saleProcessed = true;
                displaySaleInfo();
            } else {
                System.out.println("Sale cannot be processed due to invalid product or quantity.");
            }
        } else {
            System.out.println("This sale has already been processed.");
        }
    }

    public void complexDiscountLogic() {
        if (product != null) {
            if (quantity > 10) {
                totalAmount *= 0.85; // 15% discount for bulk purchase
            } else if (quantity > 5) {
                totalAmount *= 0.9; // 10% discount for moderate purchase
            } else {
                if (customer.isVIP()) {
                    totalAmount *= 0.95; // 5% discount for VIP customers
                }
            }
        }
    }

    public void displaySaleInfo() {
        //System.out.println("Sale processed for " + customer.getName() + ". Total Amount: " + totalAmount);
    }
}