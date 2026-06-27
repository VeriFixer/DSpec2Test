// Dafny_Verify_tmp_tmphq7j0row_AI_agent_verify_examples_Cube.dfy

method {:testEntry} Cube(n: nat) returns (c: nat)
  ensures c == n * n * n
{
  c := 0;
  var i := 0;
  var k := 1;
  var m := 6;
  while i <= n
    invariant 0 <= i <= n
    invariant c == i * i * i
    invariant k == 3 * i * i + 3 * i + 1
    invariant m == 6 * i + 6
  {
    c, k, m := c + k, k + m, m + 6;
    i := i + 1;
  }
}


method {:test} Test0() {
var r0 := Cube(0);
expect r0 == 0 * 0 * 0;
}

// REPEAT 1 - TIME: 9.1778327 s

method {:test} Test1() {
var r0 := Cube(1);
expect r0 == 1 * 1 * 1;
}

// REPEAT 2 - TIME: 14.5752617 s

method {:test} Test2() {
var r0 := Cube(2);
expect r0 == 2 * 2 * 2;
}

// REPEAT 3 - TIME: 19.8238291 s

method {:test} Test3() {
var r0 := Cube(3);
expect r0 == 3 * 3 * 3;
}

// REPEAT 4 - TIME: 25.1366042 s

method {:test} Test4() {
var r0 := Cube(4);
expect r0 == 4 * 4 * 4;
}

// REPEAT 5 - TIME: 31.4128256 s

method {:test} Test5() {
var r0 := Cube(5);
expect r0 == 5 * 5 * 5;
}

// REPEAT 6 - TIME: 38.2191984 s

method {:test} Test6() {
var r0 := Cube(6);
expect r0 == 6 * 6 * 6;
}

// REPEAT 7 - TIME: 44.6482135 s

method {:test} Test7() {
var r0 := Cube(7);
expect r0 == 7 * 7 * 7;
}

// REPEAT 8 - TIME: 52.6156085 s

method {:test} Test8() {
var r0 := Cube(8);
expect r0 == 8 * 8 * 8;
}

// REPEAT 9 - TIME: 59.2866807 s

method {:test} Test9() {
var r0 := Cube(9);
expect r0 == 9 * 9 * 9;
}

// REPEAT 10 - TIME: 66.7819447 s
