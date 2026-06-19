// SENG2011_tmp_tmpgk5jq85q_ass1_ex7.dfy

method {:testEntry} BigFoot(step: nat)
  requires 0 < step <= 42
{
  var indx := 0;
  while indx <= 42
    invariant 0 <= indx <= step + 42 && indx % step == 0
    decreases 42 - indx
  {
  }
  assert 0 <= indx <= step + 42 && indx % step == 0 && indx > 42;
}


method {:test} Test0() {
expect 0 < 1 <= 42, "If this check fails at runtime, the test does not meet the preconditions";
BigFoot(1);
}
method {:test} Test2() {
expect 0 < 42 <= 42, "If this check fails at runtime, the test does not meet the preconditions";
BigFoot(42);
}

// REPEAT 1 - TIME: 4.810611 s

method {:test} Test5() {
expect 0 < 2 <= 42, "If this check fails at runtime, the test does not meet the preconditions";
BigFoot(2);
}

// REPEAT 2 - TIME: 5.7702092 s

method {:test} Test6() {
expect 0 < 3 <= 42, "If this check fails at runtime, the test does not meet the preconditions";
BigFoot(3);
}

// REPEAT 3 - TIME: 6.7006907 s

method {:test} Test7() {
expect 0 < 4 <= 42, "If this check fails at runtime, the test does not meet the preconditions";
BigFoot(4);
}

// REPEAT 4 - TIME: 7.5132918 s

method {:test} Test8() {
expect 0 < 5 <= 42, "If this check fails at runtime, the test does not meet the preconditions";
BigFoot(5);
}

// REPEAT 5 - TIME: 8.3525667 s

method {:test} Test9() {
expect 0 < 6 <= 42, "If this check fails at runtime, the test does not meet the preconditions";
BigFoot(6);
}

// REPEAT 6 - TIME: 9.0317004 s

method {:test} Test10() {
expect 0 < 7 <= 42, "If this check fails at runtime, the test does not meet the preconditions";
BigFoot(7);
}

// REPEAT 7 - TIME: 9.736108 s

method {:test} Test11() {
expect 0 < 8 <= 42, "If this check fails at runtime, the test does not meet the preconditions";
BigFoot(8);
}

// REPEAT 8 - TIME: 10.2897308 s

method {:test} Test12() {
expect 0 < 9 <= 42, "If this check fails at runtime, the test does not meet the preconditions";
BigFoot(9);
}

// REPEAT 9 - TIME: 10.8725425 s

method {:test} Test13() {
expect 0 < 10 <= 42, "If this check fails at runtime, the test does not meet the preconditions";
BigFoot(10);
}

// REPEAT 10 - TIME: 11.5590239 s
