// dafny-synthesis_task_id_801.dfy

method {:testEntry} CountEqualNumbers(a: int, b: int, c: int)
    returns (count: int)
  ensures count >= 0 && count <= 3
  ensures count == 3 <==> a == b && b == c
  ensures count == 2 <==> (a == b && b != c) || (a != b && b == c) || (a == c && b != c)
  ensures count == 1 <==> a != b && b != c && a != c
{
  count := 1;
  if a != b {
    count := count + 1;
  }
  if a == c {
    count := count + 1;
  }
  if a != b && b == c {
    count := count + 1;
  }
}

method {:test} Test0() {
var r0 := CountEqualNumbers(25, 26, 26);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 25 == 26 && 26 == 26;
expect r0 == 2 <==> (25 == 26 && 26 != 26) || (25 != 26 && 26 == 26) || (25 == 26 && 26 != 26);
expect r0 == 1 <==> 25 != 26 && 26 != 26 && 25 != 26;
}
method {:test} Test1() {
var r0 := CountEqualNumbers(24, 24, 25);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 24 == 24 && 24 == 25;
expect r0 == 2 <==> (24 == 24 && 24 != 25) || (24 != 24 && 24 == 25) || (24 == 25 && 24 != 25);
expect r0 == 1 <==> 24 != 24 && 24 != 25 && 24 != 25;
}
method {:test} Test2() {
var r0 := CountEqualNumbers(26, 26, 26);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 26 == 26 && 26 == 26;
expect r0 == 2 <==> (26 == 26 && 26 != 26) || (26 != 26 && 26 == 26) || (26 == 26 && 26 != 26);
expect r0 == 1 <==> 26 != 26 && 26 != 26 && 26 != 26;
}

// REPEAT 1 - TIME: 3.3848047 s
