public class ECTSCalculator {
    private static int CalculateTotal(Course[] courses){
        int sum = 0;
        for(int i = 0; i < courses.length; i++){
            sum += courses[i].getEcts();
        }

        return sum;
    }

    private static int CalculateAvg(int sum, int length){
        return sum/(length - 1); // this is a bug
    }

    public static EctsSummary CalculateSummary(Course[] courses){
        int total = CalculateTotal(courses);
        int avg = CalculateAvg(total, courses.length);

        return new EctsSummary(total, avg);
    }
}
