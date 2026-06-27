// Dafny_Verify_tmp_tmphq7j0row_AI_agent_verify_examples_Cube.dfy

method {:testEntry} Cube(n: nat) returns (c: nat)
  ensures c == n * n * n
{
  c := 0;
  var i := 0;
  var k := 1;
  var m := 6;
  while i != n
    invariant 0 <= i <= n
    invariant c == i * i * i
    invariant k == 3 * i * i + 3 * i + 1
    invariant m == 6 * i + 6
  {
    c, k, m := c - k, k + m, m + 6;
    i := i + 1;
  }
}


method {:test} Test0() {
var r0 := Cube(0);
expect r0 == 0 * 0 * 0;
}
method {:test} Test1() {
var r0 := Cube(100);
expect r0 == 100 * 100 * 100;
}

// REPEAT 1 - TIME: 6.2046754 s

method {:test} Test5() {
var r0 := Cube(101);
expect r0 == 101 * 101 * 101;
}

// REPEAT 2 - TIME: 7.3533275 s

method {:test} Test6() {
var r0 := Cube(102);
expect r0 == 102 * 102 * 102;
}

// REPEAT 3 - TIME: 8.4290661 s

method {:test} Test7() {
var r0 := Cube(103);
expect r0 == 103 * 103 * 103;
}

// REPEAT 4 - TIME: 9.2798835 s

method {:test} Test8() {
var r0 := Cube(104);
expect r0 == 104 * 104 * 104;
}

// REPEAT 5 - TIME: 10.0615043 s

method {:test} Test9() {
var r0 := Cube(105);
expect r0 == 105 * 105 * 105;
}

// REPEAT 6 - TIME: 10.7926759 s

method {:test} Test10() {
var r0 := Cube(106);
expect r0 == 106 * 106 * 106;
}

// REPEAT 7 - TIME: 11.5720964 s

method {:test} Test11() {
var r0 := Cube(107);
expect r0 == 107 * 107 * 107;
}

// REPEAT 8 - TIME: 12.402211 s

method {:test} Test12() {
var r0 := Cube(108);
expect r0 == 108 * 108 * 108;
}

// REPEAT 9 - TIME: 13.2254179 s

method {:test} Test13() {
var r0 := Cube(109);
expect r0 == 109 * 109 * 109;
}

// REPEAT 10 - TIME: 13.8540448 s
