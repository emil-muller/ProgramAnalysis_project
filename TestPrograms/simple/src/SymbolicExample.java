public class SymbolicExample {
  public static int divideByTwo(int x) {
    if (x > 0) {
      return x / 2;
    } else {
      return 0;
    }
  }

  public static void main(String[] args) {
    int input = Integer.parseInt(args[1]);
    int result = divideByTwo(input);
    System.out.println(result);
  }
}
