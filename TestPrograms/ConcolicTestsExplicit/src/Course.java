public class Course {
    public int courseNumber;
    public int ects;
    public int slot;
    public int day;
    public Course(int coursenum, int ects, int slot, int day){
        this.ects = ects;
        this.courseNumber = coursenum;
        this.slot = slot;
        this.day = day;
    }

    public static boolean ValidateCourse(Course course){
        int ects = course.ects;
        if (ects > 10){
            return false;
        } else if (ects < 0) {
            return false;
        }
        return true;
    }
}
