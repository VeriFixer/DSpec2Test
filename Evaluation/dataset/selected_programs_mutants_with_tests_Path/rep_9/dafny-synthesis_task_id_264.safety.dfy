method {:testEntry} DogYears(humanYears: int) returns (dogYears: int)
    requires humanYears >= 0
    ensures dogYears == 7 * humanYears
{
    dogYears := 7 * humanYears;
}

method {:test} Test8() {
expect 46 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DogYears(46);
expect r0 == 7 * 46;
}

// REPEAT 9 - TIME: 10.4809603 s
