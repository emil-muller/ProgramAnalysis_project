public class ScheduleBuilder {
    public static Schedule BuildSchedule(Course[] courses) throws Exception {
        Course[] scheduledCourses = new Course[5]; // 5 days in a week

        for(int i = 0; i < courses.length; i++){
            int ects = courses[i].ects;
            int day = courses[i].day;
            if(ects > 5){
                throw new Exception(); //no more than 5 ects a day for students
            }
            scheduledCourses[day] = courses[i];
        }

        return new Schedule(scheduledCourses);
    }
}
