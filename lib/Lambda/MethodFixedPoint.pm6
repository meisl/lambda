use v6;

role MethodFixedPoint {

    method iteratedApp(&method, $endCondition = *, $start = self) {
        $start, &method ... $endCondition;
    }

    # starting at $start, returns the first fixed-point of &method
    # wrt. to $endCondition,
    # ie. the first $x st. $endCondition($x, &method($x)) == True
    # where "===" is the default end condition.
    # ...or diverges if there is none...
    method mfp(&method, $endCondition = * === *, $start = self) {
        # don't call $start, should it be Callable:
        $start ~~ Callable 
            ?? (-> { $start }, &method ... $endCondition).pop
            !! (     $start,   &method ... $endCondition).pop;
    }

    #method _mfp(&method, $start = self) {
    #    my ($x, $y) = $start;
    #    $x = $y until $x === ($y = &method($x));
    #    $x;
    #}
}
