method {:testEntry} DogYears(humanYears: int) returns (dogYears: int)
    requires humanYears >= 0
    ensures dogYears == 7 * humanYears
{
    dogYears := 7 * humanYears;
}

method {:test} Test13() {
expect 108 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DogYears(108);
expect r0 == 7 * 108;
}

// REPEAT 9 - TIME: 12.0048735 s
