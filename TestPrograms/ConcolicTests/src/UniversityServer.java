public class UniversityServer {
    private UniversityCourseManager courseManager;
    private StudentManager studentManager;

    public UniversityServer(){
        studentManager = new StudentManager();
        courseManager = new UniversityCourseManager();
    }

    public void RegisterNewCourse(int coursenum, int ects, int slot, int day) throws Exception {
        Course newCourse = new Course(coursenum, ects, slot, day);
        courseManager.AddCourse(newCourse);
    }

    public void RegisterNewStudent(int id) throws Exception {
        studentManager.RegisterStudent(new Student(id));
    }

    public void EnrollStudent(int studId, int courseId) throws Exception {
        Course course = courseManager.GetCourse(courseId);
        Student student = studentManager.GetStudent(studId);
        studentManager.EnrollStudentToCourse(student, course);
    }

    public Course[] GetCourses(int studId) throws Exception {
        Student student = studentManager.GetStudent(studId);
        return studentManager.GetCourses(student);
    }

    public EctsSummary CalculateEctsSummary(int studId) throws Exception {
        Student student = studentManager.GetStudent(studId);
        Course[] courses = studentManager.GetCourses(student);

        return ECTSCalculator.CalculateSummary(courses);
    }

    public void PrintSchedule(){
        
    }
}
