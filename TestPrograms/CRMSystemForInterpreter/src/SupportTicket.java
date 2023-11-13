public class SupportTicket {
    private String issueDescription;
    private Customer customer;

    public SupportTicket(Customer newCustomer, String newIssueDescription) {
        customer = newCustomer;
        issueDescription = newIssueDescription;
    }

    public void displayTicketInfo() {
        //System.out.println("Support Ticket: " + issueDescription + ", Customer - " + customer.getName());
    }
}