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

method {:test} Test6() {
expect 0 < 21 <= 42, "If this check fails at runtime, the test does not meet the preconditions";
BigFoot(21);
}

// REPEAT 7 - TIME: 8.6392977 s
