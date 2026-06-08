method {:testEntry} DogYears(humanYears: int) returns (dogYears: int)
    requires humanYears >= 0
    ensures dogYears == 7 * humanYears
{
    dogYears := 7 * humanYears;
}

method {:test} Test6() {
expect 44 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DogYears(44);
expect r0 == 7 * 44;
}

// REPEAT 7 - TIME: 8.187437 s
