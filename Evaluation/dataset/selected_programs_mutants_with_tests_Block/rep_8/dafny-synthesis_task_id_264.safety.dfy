method {:testEntry} DogYears(humanYears: int) returns (dogYears: int)
    requires humanYears >= 0
    ensures dogYears == 7 * humanYears
{
    dogYears := 7 * humanYears;
}

method {:test} Test7() {
expect 45 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DogYears(45);
expect r0 == 7 * 45;
}

// REPEAT 8 - TIME: 6.4360644 s
