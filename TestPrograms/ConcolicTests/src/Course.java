public class Course {
    private int courseNumber;
    private int ects;
    private int slot;
    private int day;
    public Course(int coursenum, int ects, int slot, int day){
        this.ects = ects;
        this.courseNumber = coursenum;
        this.slot = slot;
        this.day = day;
    }

    public static boolean ValidateCourse(Course course){
        if (course.getEcts() > 10){
            return false;
        } else if (course.getEcts() < 0) {
            return false;
        }
        return true;
    }

    public int getCourseNumber(){
        return this.courseNumber;
    }

    public int getEcts(){
        return this.ects;
    }

    public int getSlot(){
        return this.slot;
    }

    public int getDay(){
        return this.day;
    }
}
