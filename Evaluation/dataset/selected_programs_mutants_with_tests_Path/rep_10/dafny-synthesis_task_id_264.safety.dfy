method {:testEntry} DogYears(humanYears: int) returns (dogYears: int)
    requires humanYears >= 0
    ensures dogYears == 7 * humanYears
{
    dogYears := 7 * humanYears;
}

method {:test} Test9() {
expect 47 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DogYears(47);
expect r0 == 7 * 47;
}

// REPEAT 10 - TIME: 11.203253 s
