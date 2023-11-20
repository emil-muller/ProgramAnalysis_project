public class UniversityCourseManager {
    public int courseIndex;
    public Course[] courses;

    public UniversityCourseManager(){
        courses = new Course[0];
        courseIndex = 0;
    }

    public Course GetCourse(int num) throws Exception {
        for(int i = 0; i < courses.length; i++){
            if(courses[i].courseNumber == num){
                return courses[i];
            }
        }
        throw new Exception();
    }
    public void AddCourse(Course course) throws Exception {
        if(courseIndex >= courses.length){
            ExtendCourseLength();
        }

        boolean valid = Course.ValidateCourse(course);
        if(!valid){
            throw new Exception();
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
