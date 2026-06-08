method {:testEntry} DogYears(humanYears: int) returns (dogYears: int)
    requires humanYears >= 0
    ensures dogYears == 7 * humanYears
{
    dogYears := 7 * humanYears;
}

method {:test} Test10() {
expect 105 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DogYears(105);
expect r0 == 7 * 105;
}

// REPEAT 6 - TIME: 9.6447931 s
