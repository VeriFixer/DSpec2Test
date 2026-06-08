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

// REPEAT 1 - TIME: 3.1129696 s

method {:test} Test1() {
expect 0 < 2 <= 42, "If this check fails at runtime, the test does not meet the preconditions";
BigFoot(2);
}

// REPEAT 2 - TIME: 4.0322425 s

method {:test} Test2() {
expect 0 < 3 <= 42, "If this check fails at runtime, the test does not meet the preconditions";
BigFoot(3);
}

// REPEAT 3 - TIME: 4.9281493 s

method {:test} Test3() {
expect 0 < 4 <= 42, "If this check fails at runtime, the test does not meet the preconditions";
BigFoot(4);
}

// REPEAT 4 - TIME: 5.9038651 s

method {:test} Test4() {
expect 0 < 5 <= 42, "If this check fails at runtime, the test does not meet the preconditions";
BigFoot(5);
}

// REPEAT 5 - TIME: 6.872211 s

method {:test} Test5() {
expect 0 < 6 <= 42, "If this check fails at runtime, the test does not meet the preconditions";
BigFoot(6);
}

// REPEAT 6 - TIME: 7.8156739 s

method {:test} Test6() {
expect 0 < 7 <= 42, "If this check fails at runtime, the test does not meet the preconditions";
BigFoot(7);
}

// REPEAT 7 - TIME: 8.6671677 s

method {:test} Test7() {
expect 0 < 8 <= 42, "If this check fails at runtime, the test does not meet the preconditions";
BigFoot(8);
}

// REPEAT 8 - TIME: 9.5153458 s

method {:test} Test8() {
expect 0 < 9 <= 42, "If this check fails at runtime, the test does not meet the preconditions";
BigFoot(9);
}

// REPEAT 9 - TIME: 10.2645507 s

method {:test} Test9() {
expect 0 < 10 <= 42, "If this check fails at runtime, the test does not meet the preconditions";
BigFoot(10);
}

// REPEAT 10 - TIME: 11.0812645 s
