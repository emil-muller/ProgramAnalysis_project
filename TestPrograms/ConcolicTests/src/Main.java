public class Main {
    public static void main(String[] args) throws Exception {
        System.out.println("Hello world!");
        RegisterStudent(5);
        RegisterCourse(5);
        try{
            RegisterCourse(50);
            System.out.println("ERROR no exception thrown");
            return;
        } catch (Exception e){
            // it threw exception so we good
        }
        RegisterStudentPotentialError(1, 2);
        try{
            RegisterStudentPotentialError(1, 1);
            System.out.println("ERROR no exception thrown");
            return;
        } catch (Exception e){
            // it threw exception so we good
        }
        EnrollStudent(1);
        EnrollStudent(1,1);
        GetCourses(1);
        CalculateSummary(1);

        try{
            CalculateSummaryError(1, 1);
            System.out.println("ERROR no exception thrown");
            return;
        } catch (Exception e){
            // we good
        }
    }

    /**------------------
     * University Tests |
     * -----------------|
     */
    public static void RegisterCourse(int ects) throws Exception {
        UniversityServer server = new UniversityServer();
        server.RegisterNewCourse(101, ects, 1, 1);
    }

    //should just be simple
    public static void RegisterStudent(int id) throws Exception {
        UniversityServer server = new UniversityServer();
        server.RegisterNewStudent(id);
    }

    //if you register two student with the same id we get exception
    public static void RegisterStudentPotentialError(int id1, int id2) throws Exception {
        UniversityServer server = new UniversityServer();
        server.RegisterNewStudent(id1);
        server.RegisterNewStudent(id2);
    }

    //create courses and student and enroll student
    public static void EnrollStudent(int id) throws Exception {
        UniversityServer server = new UniversityServer();
        server.RegisterNewStudent(id);
        server.RegisterNewCourse(1, 5, 1, 1);
        server.RegisterNewCourse(2, 7, 1, 1);
        server.EnrollStudent(id, 1);
        server.EnrollStudent(id, 2);
    }

    //Again create courses and student and enroll student but more complex
    public static void EnrollStudent(int id, int courseId) throws Exception {
        UniversityServer server = new UniversityServer();
        server.RegisterNewStudent(id);
        server.RegisterNewCourse(courseId, 5, 1, 1);
        server.EnrollStudent(id, courseId);
    }

    //Get courses
    public static void GetCourses(int id) throws Exception {
        UniversityServer server = new UniversityServer();
        server.RegisterNewStudent(id);
        server.RegisterNewCourse(1, 5, 1, 1);
        server.RegisterNewCourse(2, 7, 1, 1);
        server.EnrollStudent(id, 1);
        server.EnrollStudent(id, 2);
        server.GetCourses(id);
    }

    // calculate summary no problems
    public static void CalculateSummary(int id) throws Exception {
        UniversityServer server = new UniversityServer();
        server.RegisterNewStudent(id);
        server.RegisterNewCourse(1, 5, 1, 1);
        server.RegisterNewCourse(2, 7, 1, 1);
        server.EnrollStudent(id, 1);
        server.EnrollStudent(id, 2);
        server.CalculateEctsSummary(id);
    }

    // possible div 0 error
    public static void CalculateSummaryError(int id, int courseCount) throws Exception {
        UniversityServer server = new UniversityServer();
        server.RegisterNewStudent(id);

        for(int i = 0; i < courseCount; i ++){
            server.RegisterNewCourse(i, 7, 1, 1);
            server.EnrollStudent(id, i);
        }

        server.CalculateEctsSummary(id);
    }

    /**
     * Assertion errors
     * Div 0 errors
     * Exceptions
     * Out of range indexing
     */
     public static int ErrorsTest(int a, int b, int c, int arrLen) throws Exception {
         assert c != 0; // possible assertion error
         int d = a/b; // division by 0 possible
         if(d == 2){
             throw new Exception("I dont like that number"); // possible thrown exception
         } else {
             int[] array = new int[arrLen];
             array[d] = 5; // out of bounds index error
         }

         return 42;
    }

    public static int TestString(String s){
        if (s == null){
            return 0;
        } else if(s == "abc"){
            return 1;
        } else{
            if(s == null){
                return 3;
            } else {
                return 2;
            }
        }
    }

    public static int TestString2(String s){
        if (s == null){
            return 0;
        } else if(s.equals("abc")){
            return 1;
        } else{
            if(s == null){
                return 3;
            } else {
                return 2;
            }
        }
    }
}

