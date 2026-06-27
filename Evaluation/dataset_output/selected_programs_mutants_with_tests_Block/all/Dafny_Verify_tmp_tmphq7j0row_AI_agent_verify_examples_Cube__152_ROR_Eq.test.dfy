// Dafny_Verify_tmp_tmphq7j0row_AI_agent_verify_examples_Cube.dfy

method {:testEntry} Cube(n: nat) returns (c: nat)
  ensures c == n * n * n
{
  c := 0;
  var i := 0;
  var k := 1;
  var m := 6;
  while i == n
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
var r0 := Cube(1797);
expect r0 == 1797 * 1797 * 1797;
}

// REPEAT 1 - TIME: 1.8158191 s

method {:test} Test1() {
var r0 := Cube(9517);
expect r0 == 9517 * 9517 * 9517;
}

// REPEAT 2 - TIME: 2.5111695 s

method {:test} Test2() {
var r0 := Cube(17237);
expect r0 == 17237 * 17237 * 17237;
}

// REPEAT 3 - TIME: 3.213311 s

method {:test} Test3() {
var r0 := Cube(24957);
expect r0 == 24957 * 24957 * 24957;
}

// REPEAT 4 - TIME: 3.7826962 s

method {:test} Test4() {
var r0 := Cube(32677);
expect r0 == 32677 * 32677 * 32677;
}

// REPEAT 5 - TIME: 4.4008444 s

method {:test} Test5() {
var r0 := Cube(40397);
expect r0 == 40397 * 40397 * 40397;
}

// REPEAT 6 - TIME: 5.0852267 s

method {:test} Test6() {
var r0 := Cube(40398);
expect r0 == 40398 * 40398 * 40398;
}

// REPEAT 7 - TIME: 5.6368373 s

method {:test} Test7() {
var r0 := Cube(40399);
expect r0 == 40399 * 40399 * 40399;
}

// REPEAT 8 - TIME: 6.1381587 s

method {:test} Test8() {
var r0 := Cube(40400);
expect r0 == 40400 * 40400 * 40400;
}

// REPEAT 9 - TIME: 6.6629957 s

method {:test} Test9() {
var r0 := Cube(48120);
expect r0 == 48120 * 48120 * 48120;
}

// REPEAT 10 - TIME: 7.2080508 s
