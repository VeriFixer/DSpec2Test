method {:testEntry} DogYears(humanYears: int) returns (dogYears: int)
    requires humanYears >= 0
    ensures dogYears == 7 * humanYears
{
    dogYears := 7 * humanYears;
}

method {:test} Test1() {
expect 39 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DogYears(39);
expect r0 == 7 * 39;
}

// REPEAT 2 - TIME: 5.1485396 s
