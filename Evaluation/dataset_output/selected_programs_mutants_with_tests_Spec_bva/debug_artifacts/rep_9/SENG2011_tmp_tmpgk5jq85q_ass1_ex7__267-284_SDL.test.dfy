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

method {:test} Test12() {
expect 0 < 9 <= 42, "If this check fails at runtime, the test does not meet the preconditions";
BigFoot(9);
}

// REPEAT 9 - TIME: 10.8725425 s
