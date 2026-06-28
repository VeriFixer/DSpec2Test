// dafny-synthesis_task_id_801.dfy

method {:testEntry} CountEqualNumbers(a: int, b: int, c: int)
    returns (count: int)
  ensures count >= 0 && count <= 3
  ensures count == 3 <==> a == b && b == c
  ensures count == 2 <==> (a == b && b != c) || (a != b && b == c) || (a == c && b != c)
  ensures count == 1 <==> a != b && b != c && a != c
{
  count := 1;
  if a == b {
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

// REPEAT 1 - TIME: 3.1547425 s

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

// REPEAT 2 - TIME: 4.791068 s

method {:test} Test5() {
var r0 := CountEqualNumbers(29, 30, 30);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 29 == 30 && 30 == 30;
expect r0 == 2 <==> (29 == 30 && 30 != 30) || (29 != 30 && 30 == 30) || (29 == 30 && 30 != 30);
expect r0 == 1 <==> 29 != 30 && 30 != 30 && 29 != 30;
}
method {:test} Test6() {
var r0 := CountEqualNumbers(30, 30, 30);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 30 == 30 && 30 == 30;
expect r0 == 2 <==> (30 == 30 && 30 != 30) || (30 != 30 && 30 == 30) || (30 == 30 && 30 != 30);
expect r0 == 1 <==> 30 != 30 && 30 != 30 && 30 != 30;
}

// REPEAT 3 - TIME: 6.4516316 s

method {:test} Test7() {
var r0 := CountEqualNumbers(31, 32, 32);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 31 == 32 && 32 == 32;
expect r0 == 2 <==> (31 == 32 && 32 != 32) || (31 != 32 && 32 == 32) || (31 == 32 && 32 != 32);
expect r0 == 1 <==> 31 != 32 && 32 != 32 && 31 != 32;
}
method {:test} Test8() {
var r0 := CountEqualNumbers(31, 31, 31);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 31 == 31 && 31 == 31;
expect r0 == 2 <==> (31 == 31 && 31 != 31) || (31 != 31 && 31 == 31) || (31 == 31 && 31 != 31);
expect r0 == 1 <==> 31 != 31 && 31 != 31 && 31 != 31;
}

// REPEAT 4 - TIME: 7.8327675 s

method {:test} Test9() {
var r0 := CountEqualNumbers(33, 34, 34);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 33 == 34 && 34 == 34;
expect r0 == 2 <==> (33 == 34 && 34 != 34) || (33 != 34 && 34 == 34) || (33 == 34 && 34 != 34);
expect r0 == 1 <==> 33 != 34 && 34 != 34 && 33 != 34;
}
method {:test} Test10() {
var r0 := CountEqualNumbers(33, 33, 33);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 33 == 33 && 33 == 33;
expect r0 == 2 <==> (33 == 33 && 33 != 33) || (33 != 33 && 33 == 33) || (33 == 33 && 33 != 33);
expect r0 == 1 <==> 33 != 33 && 33 != 33 && 33 != 33;
}

// REPEAT 5 - TIME: 8.8962595 s

method {:test} Test11() {
var r0 := CountEqualNumbers(36, 35, 35);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 36 == 35 && 35 == 35;
expect r0 == 2 <==> (36 == 35 && 35 != 35) || (36 != 35 && 35 == 35) || (36 == 35 && 35 != 35);
expect r0 == 1 <==> 36 != 35 && 35 != 35 && 36 != 35;
}
method {:test} Test12() {
var r0 := CountEqualNumbers(35, 35, 35);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 35 == 35 && 35 == 35;
expect r0 == 2 <==> (35 == 35 && 35 != 35) || (35 != 35 && 35 == 35) || (35 == 35 && 35 != 35);
expect r0 == 1 <==> 35 != 35 && 35 != 35 && 35 != 35;
}

// REPEAT 6 - TIME: 10.1240866 s

method {:test} Test13() {
var r0 := CountEqualNumbers(37, 38, 38);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 37 == 38 && 38 == 38;
expect r0 == 2 <==> (37 == 38 && 38 != 38) || (37 != 38 && 38 == 38) || (37 == 38 && 38 != 38);
expect r0 == 1 <==> 37 != 38 && 38 != 38 && 37 != 38;
}
method {:test} Test14() {
var r0 := CountEqualNumbers(38, 38, 37);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 38 == 38 && 38 == 37;
expect r0 == 2 <==> (38 == 38 && 38 != 37) || (38 != 38 && 38 == 37) || (38 == 37 && 38 != 37);
expect r0 == 1 <==> 38 != 38 && 38 != 37 && 38 != 37;
}
method {:test} Test15() {
var r0 := CountEqualNumbers(37, 37, 37);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 37 == 37 && 37 == 37;
expect r0 == 2 <==> (37 == 37 && 37 != 37) || (37 != 37 && 37 == 37) || (37 == 37 && 37 != 37);
expect r0 == 1 <==> 37 != 37 && 37 != 37 && 37 != 37;
}

// REPEAT 7 - TIME: 11.3573941 s

method {:test} Test16() {
var r0 := CountEqualNumbers(40, 39, 39);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 40 == 39 && 39 == 39;
expect r0 == 2 <==> (40 == 39 && 39 != 39) || (40 != 39 && 39 == 39) || (40 == 39 && 39 != 39);
expect r0 == 1 <==> 40 != 39 && 39 != 39 && 40 != 39;
}
method {:test} Test17() {
var r0 := CountEqualNumbers(40, 40, 39);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 40 == 40 && 40 == 39;
expect r0 == 2 <==> (40 == 40 && 40 != 39) || (40 != 40 && 40 == 39) || (40 == 39 && 40 != 39);
expect r0 == 1 <==> 40 != 40 && 40 != 39 && 40 != 39;
}
method {:test} Test18() {
var r0 := CountEqualNumbers(40, 39, 40);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 40 == 39 && 39 == 40;
expect r0 == 2 <==> (40 == 39 && 39 != 40) || (40 != 39 && 39 == 40) || (40 == 40 && 39 != 40);
expect r0 == 1 <==> 40 != 39 && 39 != 40 && 40 != 40;
}

// REPEAT 8 - TIME: 12.9707655 s

method {:test} Test19() {
var r0 := CountEqualNumbers(41, 42, 42);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 41 == 42 && 42 == 42;
expect r0 == 2 <==> (41 == 42 && 42 != 42) || (41 != 42 && 42 == 42) || (41 == 42 && 42 != 42);
expect r0 == 1 <==> 41 != 42 && 42 != 42 && 41 != 42;
}
method {:test} Test20() {
var r0 := CountEqualNumbers(41, 41, 41);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 41 == 41 && 41 == 41;
expect r0 == 2 <==> (41 == 41 && 41 != 41) || (41 != 41 && 41 == 41) || (41 == 41 && 41 != 41);
expect r0 == 1 <==> 41 != 41 && 41 != 41 && 41 != 41;
}

// REPEAT 9 - TIME: 13.9320118 s

method {:test} Test21() {
var r0 := CountEqualNumbers(44, 46, 46);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 44 == 46 && 46 == 46;
expect r0 == 2 <==> (44 == 46 && 46 != 46) || (44 != 46 && 46 == 46) || (44 == 46 && 46 != 46);
expect r0 == 1 <==> 44 != 46 && 46 != 46 && 44 != 46;
}
method {:test} Test22() {
var r0 := CountEqualNumbers(43, 43, 43);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 43 == 43 && 43 == 43;
expect r0 == 2 <==> (43 == 43 && 43 != 43) || (43 != 43 && 43 == 43) || (43 == 43 && 43 != 43);
expect r0 == 1 <==> 43 != 43 && 43 != 43 && 43 != 43;
}

// REPEAT 10 - TIME: 14.9425314 s
