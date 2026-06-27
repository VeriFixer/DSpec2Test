// dafny-synthesis_task_id_801.dfy

method {:testEntry} CountEqualNumbers(a: int, b: int, c: int)
    returns (count: int)
  ensures count >= 0 && count <= 3
  ensures count == 3 <==> a == b && b == c
  ensures count == 2 <==> (a == b && b != c) || (a != b && b == c) || (a == c && b != c)
  ensures count == 1 <==> a != b && b != c && a != c
{
  count := 1;
  if a >= b {
    count := count + 1;
  }
  if a == c {
    count := count + 1;
  }
  if a != b && b == c {
    count := count + 1;
  }
}

method {:test} Test3() {
var r0 := CountEqualNumbers(28, 27, 27);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 28 == 27 && 27 == 27;
expect r0 == 2 <==> (28 == 27 && 27 != 27) || (28 != 27 && 27 == 27) || (28 == 27 && 27 != 27);
expect r0 == 1 <==> 28 != 27 && 27 != 27 && 28 != 27;
}
method {:test} Test4() {
var r0 := CountEqualNumbers(27, 27, 27);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 27 == 27 && 27 == 27;
expect r0 == 2 <==> (27 == 27 && 27 != 27) || (27 != 27 && 27 == 27) || (27 == 27 && 27 != 27);
expect r0 == 1 <==> 27 != 27 && 27 != 27 && 27 != 27;
}

// REPEAT 2 - TIME: 4.838994 s
