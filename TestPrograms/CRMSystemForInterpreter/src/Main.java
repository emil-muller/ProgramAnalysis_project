public class Main {
    public static void main(String[] args) {

        System.out.println("Hello world!");
        for(int i = 1; i < 8; i++){
            CallTests(i);
        }
    }

    public static void CallTests(int test){
        CRMSystem crm = new CRMSystem(20, 10, 20, 20, 10);

        if(test == 1) {
            testStandardSaleProcessing(crm);
        } else if (test == 2) {
            testDiscountedSaleProcessing(crm);
        } else if (test == 3) {
            testInvalidProductSale(crm);
        } else if (test == 4) {
            testInvalidQuantitySale(crm);
        } else if (test == 5) {
            testReprocessingSale(crm);
        } else if (test == 6) {
            testComplexDiscountLogic(crm);
        } else if (test == 7) {
            testAddCustomer(crm);
        }
    }

    /**
     * testStandardSaleProcessing tests a normal sale process.
     * Sequence Diagram:
     * - CRMSystem -> Sale: processSale()
     * - Sale -> Product: getPrice()
     * - Sale -> Customer: getName()
     * - Sale -> System: println()
     */
    private static void testStandardSaleProcessing(CRMSystem crm) {
        Customer customer = new Customer("Frank", "frank@example.com", false);
        Product product = new Product("StandardProduct", 50.00);
        Sale sale = new Sale(customer, product, 2);

        crm.processSale(sale);
    }

    /**
     * testDiscountedSaleProcessing tests a sale process where discounts are applied.
     * Sequence Diagram:
     * - CRMSystem -> Sale: processSale()
     * - Sale -> Product: getPrice()
     * - Sale: complexDiscountLogic() (internal decision-making)
     * - Sale -> Customer: isVIP(), getName()
     * - Sale -> System: println()
     */
    private static void testDiscountedSaleProcessing(CRMSystem crm) {
        Customer customer = new Customer("Grace", "grace@example.com", false);
        Product product = new Product("DiscountedProduct", 100.00);
        Sale sale = new Sale(customer, product, 10); // Quantity to trigger discount

        crm.processSale(sale);
    }

    /**
     * testInvalidProductSale tests the sale process with a null product, leading to an early exit.
     * Sequence Diagram:
     * - CRMSystem -> Sale: processSale()
     * - Sale -> System: println() (Invalid product or quantity message)
     */
    private static void testInvalidProductSale(CRMSystem crm) {
        Customer customer = new Customer("Harry", "harry@example.com", false);
        Sale sale = new Sale(customer, null, 3);

        crm.processSale(sale);
    }

    /**
     * testInvalidQuantitySale tests the sale process with an invalid quantity.
     * Sequence Diagram:
     * - CRMSystem -> Sale: processSale()
     * - Sale -> System: println() (Invalid product or quantity message)
     */
    private static void testInvalidQuantitySale(CRMSystem crm) {
        Customer customer = new Customer("Irene", "irene@example.com", false);
        Product product = new Product("InvalidQuantityProduct", 20.00);
        Sale sale = new Sale(customer, product, 0);

        crm.processSale(sale);
    }

    /**
     * testReprocessingSale tests the scenario where a sale is processed more than once.
     * Sequence Diagram:
     * - CRMSystem -> Sale: processSale()
     * - Sale -> Product: getPrice()
     * - Sale -> Customer: getName()
     * - Sale -> System: println()
     * - CRMSystem -> Sale: processSale() (second call)
     * - Sale -> System: println() (Already processed message)
     */
    private static void testReprocessingSale(CRMSystem crm) {
        Customer customer = new Customer("Jack", "jack@example.com", false);
        Product product = new Product("ReprocessProduct", 30.00);
        Sale sale = new Sale(customer, product, 1);

        crm.processSale(sale); // First processing
        crm.processSale(sale); // Attempt to reprocess
    }

    /**
     * testComplexDiscountLogic tests the complex discount logic in the sale process.
     * Sequence Diagram:
     * - CRMSystem -> Sale: processSale()
     * - Sale -> Product: getPrice()
     * - Sale: complexDiscountLogic() (internal decision-making with multiple branches)
     * - Sale -> Customer: isVIP(), getName()
     * - Sale -> System: println()
     */
    private static void testComplexDiscountLogic(CRMSystem crm) {
        Customer vipCustomer = new Customer("VIPCustomer", "vip@example.com", true);
        Product expensiveProduct = new Product("ExpensiveProduct", 500.00);
        Sale vipSale = new Sale(vipCustomer, expensiveProduct, 3);

        crm.processSale(vipSale);
        vipSale.complexDiscountLogic();
    }

    /**
     * testAddCustomer tests adding a customer to the CRM system.
     * Sequence Diagram:
     * - CRMSystem -> Customer[]
     * - Customer -> System: println() (Displaying info)
     */
    private static void testAddCustomer(CRMSystem crm) {
        Customer newCustomer = new Customer("Kyle", "kyle@example.com", false);
        crm.addCustomer(newCustomer);
        newCustomer.displayInfo();
    }
}