method {:testEntry} DogYears(humanYears: int) returns (dogYears: int)
    requires humanYears >= 0
    ensures dogYears == 7 * humanYears
{
    dogYears := 7 * humanYears;
}

method {:test} Test2() {
expect 40 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DogYears(40);
expect r0 == 7 * 40;
}

// REPEAT 3 - TIME: 3.5805482 s
