// successfully verifies
method {:testEntry} BigFoot(step: nat) // DO NOT CHANGE
requires 0 < step <= 42;
{
    var indx := 0; // DO NOT CHANGE
    while indx<=42 // DO NOT CHANGE
    invariant 0 <= indx <= step + 42 && indx % step == 0
    decreases 42 - indx
    { indx := indx+step; } // DO NOT CHANGE
    assert 0 <= indx <= step + 42 && indx % step == 0 && indx > 42;
}

method {:test} Test0() {
expect 0 < 1 <= 42, "If this check fails at runtime, the test does not meet the preconditions";
BigFoot(1);
}

// REPEAT 1 - TIME: 2.6564275 s

method {:test} Test1() {
expect 0 < 2 <= 42, "If this check fails at runtime, the test does not meet the preconditions";
BigFoot(2);
}

// REPEAT 2 - TIME: 3.7488549 s

method {:test} Test2() {
expect 0 < 42 <= 42, "If this check fails at runtime, the test does not meet the preconditions";
BigFoot(42);
}

// REPEAT 3 - TIME: 4.777046 s

method {:test} Test3() {
expect 0 < 3 <= 42, "If this check fails at runtime, the test does not meet the preconditions";
BigFoot(3);
}

// REPEAT 4 - TIME: 5.9815662 s

method {:test} Test4() {
expect 0 < 4 <= 42, "If this check fails at runtime, the test does not meet the preconditions";
BigFoot(4);
}

// REPEAT 5 - TIME: 6.9736462 s

method {:test} Test5() {
expect 0 < 5 <= 42, "If this check fails at runtime, the test does not meet the preconditions";
BigFoot(5);
}

// REPEAT 6 - TIME: 7.8825817 s

method {:test} Test6() {
expect 0 < 21 <= 42, "If this check fails at runtime, the test does not meet the preconditions";
BigFoot(21);
}

// REPEAT 7 - TIME: 8.6392977 s

method {:test} Test7() {
expect 0 < 22 <= 42, "If this check fails at runtime, the test does not meet the preconditions";
BigFoot(22);
}

// REPEAT 8 - TIME: 9.3521884 s

method {:test} Test8() {
expect 0 < 23 <= 42, "If this check fails at runtime, the test does not meet the preconditions";
BigFoot(23);
}

// REPEAT 9 - TIME: 10.1514857 s

method {:test} Test9() {
expect 0 < 24 <= 42, "If this check fails at runtime, the test does not meet the preconditions";
BigFoot(24);
}

// REPEAT 10 - TIME: 10.8673014 s
