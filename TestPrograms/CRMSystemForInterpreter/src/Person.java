public abstract class Person {
    protected String name;
    protected String email;

    public Person(String newName, String newEmail) {
        name = newName;
        email = newEmail;
    }

    public abstract void displayInfo();
}
