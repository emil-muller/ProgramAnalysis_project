public class UniversityCourseManager {
    private int courseIndex;
    private Course[] courses;

    public UniversityCourseManager(){
        courses = new Course[0];
        courseIndex = 0;
    }

    public Course GetCourse(int num) throws Exception {
        for(int i = 0; i < courses.length; i++){
            if(courses[i].getCourseNumber() == num){
                return courses[i];
            }
        }
        throw new Exception();
    }
    public void AddCourse(Course course) throws Exception {
        if(courseIndex >= courses.length){
            ExtendCourseLength();
        }

        if(!Course.ValidateCourse(course)){
            InvalidCourseAdd.ThrowException();
        }

        courses[courseIndex] = course;
        courseIndex += 1;
    }

    private void ExtendCourseLength(){
        Course[] newCourseList = new Course[courses.length + 1];
        for(int i = 0; i < courses.length; i ++){
            newCourseList[i] = courses[i];
        }

        this.courses = newCourseList;
    }
}
