public class StudentCourseMapping {
    private Student student;
    private Course course;

    public StudentCourseMapping(Student student, Course course){
        this.student = student;
        this.course = course;
    }

    public Student getStudent(){
        return student;
    }

    public Course getCourse(){
        return course;
    }
}
