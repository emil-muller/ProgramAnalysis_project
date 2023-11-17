public class StudentManager {
    private int studentIndex;
    private int mappingIndex;
    private Student[] students;
    private StudentCourseMapping[] enrollments;
    public StudentManager(){
        students = new Student[0];
        enrollments = new StudentCourseMapping[0];
        studentIndex = 0;
        mappingIndex = 0;
    }

    public void EnrollStudentToCourse(Student student, Course course){
        if(mappingIndex >= enrollments.length){
            ExtendStudentMappingLength();
        }
        // maybe check if both student and course exists
        StudentCourseMapping mapping = new StudentCourseMapping(student, course);
        enrollments[mappingIndex] = mapping;
        mappingIndex += 1;
    }

    public void RegisterStudent(Student student) throws Exception {
        for(int i = 0; i < students.length; i++){
            if(students[i].getID() == student.getID()){
                StudentAlreadyExistsException.ThrowException();
            }
        }

        if(studentIndex >= students.length){
            ExtendStudentLength();
        }

        students[studentIndex] = student;
        studentIndex += 1;
    }

    public Student GetStudent(int id) throws Exception {
        for(int i = 0; i < students.length; i++){
            if(students[i].getID() == id){
                return students[i];
            }
        }

        throw new Exception();
    }

    public Course[] GetCourses(Student student){
        int count = 0;
        for(int i = 0; i < enrollments.length; i++){
            if(enrollments[i].getStudent().getID() == student.getID()){
                count += 1;
            }
        }

        if(count == 0) {
            return new Course[0];
        }

        Course[] courses = new Course[count];
        for(int i = 0; i < enrollments.length; i++){
            if(enrollments[i].getStudent().getID() == student.getID()){
                courses[i] = enrollments[i].getCourse();
            }
        }

        return courses;
    }

    private void ExtendStudentLength(){
        Student[] newStudentLength = new Student[students.length + 1];
        for(int i = 0; i < students.length; i ++){
            newStudentLength[i] = students[i];
        }

        this.students = newStudentLength;
    }

    private void ExtendStudentMappingLength(){
        StudentCourseMapping[] newStudentMappingLength = new StudentCourseMapping[enrollments.length + 1];
        for(int i = 0; i < enrollments.length; i ++){
            newStudentMappingLength[i] = enrollments[i];
        }

        this.enrollments = newStudentMappingLength;
    }
}
