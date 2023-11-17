public class Schedule {
    private Course[] courses;

    private Schedule(Course[] courses){
        this.courses = courses;
    }

    public void printSchedule() throws Exception {
        assert courses.length > 0;

        if(courses.length < 1){
            NoCoursesException.ThrowException();
        }

        for(int i = 0; i < courses.length; i++){
            System.out.println("Course info");
        }
    }
}
