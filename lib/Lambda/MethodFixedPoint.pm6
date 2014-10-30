use v6;

role MethodFixedPoint {

    # starting at $start, returns a lazy list of iterated applications
    # of &method, ending with the first fixed-point (listed twice)
    # or infinite if there is none.
    method iteratedApp(&method, $endCondition = * === *, $start = self) {
        gather {
        my ($x, $y) = take $start;
            $x = $y until $endCondition($x, take $y = &method($x));
        }
    }


    # starting at $start, returns the first fixed-point of &method
    # wrt. to $endCondition,
    # ie. the first $x st. $endCondition($x, &method($x)) == True
    # where "===" is the default end condition.
    # ...or diverges if there is none...
    method mfp(&method, $endCondition = * === *, $start = self) {
        self.iteratedApp(&method, $endCondition, $start).pop;
        #my ($x, $y) = $start;
        #$x = $y until $endCondition($x, $y = &method($x));
        #$x;
    }
}
