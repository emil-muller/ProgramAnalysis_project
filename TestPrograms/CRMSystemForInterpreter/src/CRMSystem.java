public class CRMSystem {
    private Customer[] customers;
    private Employee[] employees;
    private Product[] products;
    private Sale[] sales;
    private SupportTicket[] tickets;
    private int customerCount, employeeCount, productCount, saleCount, ticketCount;

    public CRMSystem(int customerSize, int employeeSize, int productSize, int saleSize, int ticketSize) {
        customers = new Customer[customerSize];
        employees = new Employee[employeeSize];
        products = new Product[productSize];
        sales = new Sale[saleSize];
        tickets = new SupportTicket[ticketSize];
        customerCount = employeeCount = productCount = saleCount = ticketCount = 0;
    }

    public void addCustomer(Customer customer) {
        if (customerCount < customers.length) {
            customers[customerCount++] = customer;
        }
    }

    public void addEmployee(Employee employee) {
        if (employeeCount < employees.length) {
            employees[employeeCount++] = employee;
        }
    }

    public void addProduct(Product product) {
        if (productCount < products.length) {
            products[productCount++] = product;
        }
    }

    public void addSale(Sale sale) {
        if (saleCount < sales.length) {
            sales[saleCount++] = sale;
        }
    }

    public void processSale(Sale sale) {
        sale.processSale();
    }

    public void addTicket(SupportTicket ticket) {
        if (ticketCount < tickets.length) {
            tickets[ticketCount++] = ticket;
        }
    }
}