// dafny-synthesis_task_id_801.dfy

method {:testEntry} CountEqualNumbers(a: int, b: int, c: int)
    returns (count: int)
  ensures count >= 0 && count <= 3
  ensures count == 3 <==> a == b && b == c
  ensures count == 2 <==> (a == b && b != c) || (a != b && b == c) || (a == c && b != c)
  ensures count == 1 <==> a != b && b != c && a != c
{
  count := 1;
  if a < b {
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
var r0 := CountEqualNumbers(24, 24, 24);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 24 == 24 && 24 == 24;
expect r0 == 2 <==> (24 == 24 && 24 != 24) || (24 != 24 && 24 == 24) || (24 == 24 && 24 != 24);
expect r0 == 1 <==> 24 != 24 && 24 != 24 && 24 != 24;
}
method {:test} Test1() {
var r0 := CountEqualNumbers(25, 25, 26);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 25 == 25 && 25 == 26;
expect r0 == 2 <==> (25 == 25 && 25 != 26) || (25 != 25 && 25 == 26) || (25 == 26 && 25 != 26);
expect r0 == 1 <==> 25 != 25 && 25 != 26 && 25 != 26;
}
method {:test} Test2() {
var r0 := CountEqualNumbers(25, 24, 25);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 25 == 24 && 24 == 25;
expect r0 == 2 <==> (25 == 24 && 24 != 25) || (25 != 24 && 24 == 25) || (25 == 25 && 24 != 25);
expect r0 == 1 <==> 25 != 24 && 24 != 25 && 25 != 25;
}
method {:test} Test3() {
var r0 := CountEqualNumbers(25, 26, 26);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 25 == 26 && 26 == 26;
expect r0 == 2 <==> (25 == 26 && 26 != 26) || (25 != 26 && 26 == 26) || (25 == 26 && 26 != 26);
expect r0 == 1 <==> 25 != 26 && 26 != 26 && 25 != 26;
}
method {:test} Test4() {
var r0 := CountEqualNumbers(24, 25, 26);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 24 == 25 && 25 == 26;
expect r0 == 2 <==> (24 == 25 && 25 != 26) || (24 != 25 && 25 == 26) || (24 == 26 && 25 != 26);
expect r0 == 1 <==> 24 != 25 && 25 != 26 && 24 != 26;
}

// REPEAT 1 - TIME: 6.2242432 s

method {:test} Test5() {
var r0 := CountEqualNumbers(29, 29, 29);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 29 == 29 && 29 == 29;
expect r0 == 2 <==> (29 == 29 && 29 != 29) || (29 != 29 && 29 == 29) || (29 == 29 && 29 != 29);
expect r0 == 1 <==> 29 != 29 && 29 != 29 && 29 != 29;
}
method {:test} Test6() {
var r0 := CountEqualNumbers(28, 28, 29);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 28 == 28 && 28 == 29;
expect r0 == 2 <==> (28 == 28 && 28 != 29) || (28 != 28 && 28 == 29) || (28 == 29 && 28 != 29);
expect r0 == 1 <==> 28 != 28 && 28 != 29 && 28 != 29;
}
method {:test} Test7() {
var r0 := CountEqualNumbers(28, 27, 28);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 28 == 27 && 27 == 28;
expect r0 == 2 <==> (28 == 27 && 27 != 28) || (28 != 27 && 27 == 28) || (28 == 28 && 27 != 28);
expect r0 == 1 <==> 28 != 27 && 27 != 28 && 28 != 28;
}
method {:test} Test8() {
var r0 := CountEqualNumbers(28, 27, 27);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 28 == 27 && 27 == 27;
expect r0 == 2 <==> (28 == 27 && 27 != 27) || (28 != 27 && 27 == 27) || (28 == 27 && 27 != 27);
expect r0 == 1 <==> 28 != 27 && 27 != 27 && 28 != 27;
}
method {:test} Test9() {
var r0 := CountEqualNumbers(29, 27, 28);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 29 == 27 && 27 == 28;
expect r0 == 2 <==> (29 == 27 && 27 != 28) || (29 != 27 && 27 == 28) || (29 == 28 && 27 != 28);
expect r0 == 1 <==> 29 != 27 && 27 != 28 && 29 != 28;
}

// REPEAT 2 - TIME: 10.3028629 s

method {:test} Test10() {
var r0 := CountEqualNumbers(31, 31, 31);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 31 == 31 && 31 == 31;
expect r0 == 2 <==> (31 == 31 && 31 != 31) || (31 != 31 && 31 == 31) || (31 == 31 && 31 != 31);
expect r0 == 1 <==> 31 != 31 && 31 != 31 && 31 != 31;
}
method {:test} Test11() {
var r0 := CountEqualNumbers(32, 32, 30);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 32 == 32 && 32 == 30;
expect r0 == 2 <==> (32 == 32 && 32 != 30) || (32 != 32 && 32 == 30) || (32 == 30 && 32 != 30);
expect r0 == 1 <==> 32 != 32 && 32 != 30 && 32 != 30;
}
method {:test} Test12() {
var r0 := CountEqualNumbers(30, 31, 30);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 30 == 31 && 31 == 30;
expect r0 == 2 <==> (30 == 31 && 31 != 30) || (30 != 31 && 31 == 30) || (30 == 30 && 31 != 30);
expect r0 == 1 <==> 30 != 31 && 31 != 30 && 30 != 30;
}
method {:test} Test13() {
var r0 := CountEqualNumbers(31, 30, 30);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 31 == 30 && 30 == 30;
expect r0 == 2 <==> (31 == 30 && 30 != 30) || (31 != 30 && 30 == 30) || (31 == 30 && 30 != 30);
expect r0 == 1 <==> 31 != 30 && 30 != 30 && 31 != 30;
}
method {:test} Test14() {
var r0 := CountEqualNumbers(32, 31, 30);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 32 == 31 && 31 == 30;
expect r0 == 2 <==> (32 == 31 && 31 != 30) || (32 != 31 && 31 == 30) || (32 == 30 && 31 != 30);
expect r0 == 1 <==> 32 != 31 && 31 != 30 && 32 != 30;
}

// REPEAT 3 - TIME: 14.0242 s

method {:test} Test15() {
var r0 := CountEqualNumbers(34, 34, 34);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 34 == 34 && 34 == 34;
expect r0 == 2 <==> (34 == 34 && 34 != 34) || (34 != 34 && 34 == 34) || (34 == 34 && 34 != 34);
expect r0 == 1 <==> 34 != 34 && 34 != 34 && 34 != 34;
}
method {:test} Test16() {
var r0 := CountEqualNumbers(33, 33, 35);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 33 == 33 && 33 == 35;
expect r0 == 2 <==> (33 == 33 && 33 != 35) || (33 != 33 && 33 == 35) || (33 == 35 && 33 != 35);
expect r0 == 1 <==> 33 != 33 && 33 != 35 && 33 != 35;
}
method {:test} Test17() {
var r0 := CountEqualNumbers(34, 33, 34);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 34 == 33 && 33 == 34;
expect r0 == 2 <==> (34 == 33 && 33 != 34) || (34 != 33 && 33 == 34) || (34 == 34 && 33 != 34);
expect r0 == 1 <==> 34 != 33 && 33 != 34 && 34 != 34;
}
method {:test} Test18() {
var r0 := CountEqualNumbers(33, 34, 34);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 33 == 34 && 34 == 34;
expect r0 == 2 <==> (33 == 34 && 34 != 34) || (33 != 34 && 34 == 34) || (33 == 34 && 34 != 34);
expect r0 == 1 <==> 33 != 34 && 34 != 34 && 33 != 34;
}
method {:test} Test19() {
var r0 := CountEqualNumbers(33, 34, 35);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 33 == 34 && 34 == 35;
expect r0 == 2 <==> (33 == 34 && 34 != 35) || (33 != 34 && 34 == 35) || (33 == 35 && 34 != 35);
expect r0 == 1 <==> 33 != 34 && 34 != 35 && 33 != 35;
}

// REPEAT 4 - TIME: 17.6542064 s

method {:test} Test20() {
var r0 := CountEqualNumbers(36, 36, 36);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 36 == 36 && 36 == 36;
expect r0 == 2 <==> (36 == 36 && 36 != 36) || (36 != 36 && 36 == 36) || (36 == 36 && 36 != 36);
expect r0 == 1 <==> 36 != 36 && 36 != 36 && 36 != 36;
}
method {:test} Test21() {
var r0 := CountEqualNumbers(37, 37, 36);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 37 == 37 && 37 == 36;
expect r0 == 2 <==> (37 == 37 && 37 != 36) || (37 != 37 && 37 == 36) || (37 == 36 && 37 != 36);
expect r0 == 1 <==> 37 != 37 && 37 != 36 && 37 != 36;
}
method {:test} Test22() {
var r0 := CountEqualNumbers(36, 37, 36);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 36 == 37 && 37 == 36;
expect r0 == 2 <==> (36 == 37 && 37 != 36) || (36 != 37 && 37 == 36) || (36 == 36 && 37 != 36);
expect r0 == 1 <==> 36 != 37 && 37 != 36 && 36 != 36;
}
method {:test} Test23() {
var r0 := CountEqualNumbers(37, 36, 36);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 37 == 36 && 36 == 36;
expect r0 == 2 <==> (37 == 36 && 36 != 36) || (37 != 36 && 36 == 36) || (37 == 36 && 36 != 36);
expect r0 == 1 <==> 37 != 36 && 36 != 36 && 37 != 36;
}
method {:test} Test24() {
var r0 := CountEqualNumbers(38, 37, 36);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 38 == 37 && 37 == 36;
expect r0 == 2 <==> (38 == 37 && 37 != 36) || (38 != 37 && 37 == 36) || (38 == 36 && 37 != 36);
expect r0 == 1 <==> 38 != 37 && 37 != 36 && 38 != 36;
}

// REPEAT 5 - TIME: 21.3122222 s

method {:test} Test25() {
var r0 := CountEqualNumbers(39, 39, 39);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 39 == 39 && 39 == 39;
expect r0 == 2 <==> (39 == 39 && 39 != 39) || (39 != 39 && 39 == 39) || (39 == 39 && 39 != 39);
expect r0 == 1 <==> 39 != 39 && 39 != 39 && 39 != 39;
}
method {:test} Test26() {
var r0 := CountEqualNumbers(40, 40, 39);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 40 == 40 && 40 == 39;
expect r0 == 2 <==> (40 == 40 && 40 != 39) || (40 != 40 && 40 == 39) || (40 == 39 && 40 != 39);
expect r0 == 1 <==> 40 != 40 && 40 != 39 && 40 != 39;
}
method {:test} Test27() {
var r0 := CountEqualNumbers(39, 40, 39);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 39 == 40 && 40 == 39;
expect r0 == 2 <==> (39 == 40 && 40 != 39) || (39 != 40 && 40 == 39) || (39 == 39 && 40 != 39);
expect r0 == 1 <==> 39 != 40 && 40 != 39 && 39 != 39;
}
method {:test} Test28() {
var r0 := CountEqualNumbers(40, 39, 39);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 40 == 39 && 39 == 39;
expect r0 == 2 <==> (40 == 39 && 39 != 39) || (40 != 39 && 39 == 39) || (40 == 39 && 39 != 39);
expect r0 == 1 <==> 40 != 39 && 39 != 39 && 40 != 39;
}
method {:test} Test29() {
var r0 := CountEqualNumbers(41, 40, 39);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 41 == 40 && 40 == 39;
expect r0 == 2 <==> (41 == 40 && 40 != 39) || (41 != 40 && 40 == 39) || (41 == 39 && 40 != 39);
expect r0 == 1 <==> 41 != 40 && 40 != 39 && 41 != 39;
}

// REPEAT 6 - TIME: 25.4022071 s

method {:test} Test30() {
var r0 := CountEqualNumbers(42, 42, 42);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 42 == 42 && 42 == 42;
expect r0 == 2 <==> (42 == 42 && 42 != 42) || (42 != 42 && 42 == 42) || (42 == 42 && 42 != 42);
expect r0 == 1 <==> 42 != 42 && 42 != 42 && 42 != 42;
}
method {:test} Test31() {
var r0 := CountEqualNumbers(43, 43, 42);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 43 == 43 && 43 == 42;
expect r0 == 2 <==> (43 == 43 && 43 != 42) || (43 != 43 && 43 == 42) || (43 == 42 && 43 != 42);
expect r0 == 1 <==> 43 != 43 && 43 != 42 && 43 != 42;
}
method {:test} Test32() {
var r0 := CountEqualNumbers(42, 43, 42);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 42 == 43 && 43 == 42;
expect r0 == 2 <==> (42 == 43 && 43 != 42) || (42 != 43 && 43 == 42) || (42 == 42 && 43 != 42);
expect r0 == 1 <==> 42 != 43 && 43 != 42 && 42 != 42;
}
method {:test} Test33() {
var r0 := CountEqualNumbers(43, 42, 42);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 43 == 42 && 42 == 42;
expect r0 == 2 <==> (43 == 42 && 42 != 42) || (43 != 42 && 42 == 42) || (43 == 42 && 42 != 42);
expect r0 == 1 <==> 43 != 42 && 42 != 42 && 43 != 42;
}
method {:test} Test34() {
var r0 := CountEqualNumbers(44, 43, 42);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 44 == 43 && 43 == 42;
expect r0 == 2 <==> (44 == 43 && 43 != 42) || (44 != 43 && 43 == 42) || (44 == 42 && 43 != 42);
expect r0 == 1 <==> 44 != 43 && 43 != 42 && 44 != 42;
}

// REPEAT 7 - TIME: 29.3025936 s

method {:test} Test35() {
var r0 := CountEqualNumbers(45, 45, 45);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 45 == 45 && 45 == 45;
expect r0 == 2 <==> (45 == 45 && 45 != 45) || (45 != 45 && 45 == 45) || (45 == 45 && 45 != 45);
expect r0 == 1 <==> 45 != 45 && 45 != 45 && 45 != 45;
}
method {:test} Test36() {
var r0 := CountEqualNumbers(46, 46, 45);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 46 == 46 && 46 == 45;
expect r0 == 2 <==> (46 == 46 && 46 != 45) || (46 != 46 && 46 == 45) || (46 == 45 && 46 != 45);
expect r0 == 1 <==> 46 != 46 && 46 != 45 && 46 != 45;
}
method {:test} Test37() {
var r0 := CountEqualNumbers(45, 46, 45);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 45 == 46 && 46 == 45;
expect r0 == 2 <==> (45 == 46 && 46 != 45) || (45 != 46 && 46 == 45) || (45 == 45 && 46 != 45);
expect r0 == 1 <==> 45 != 46 && 46 != 45 && 45 != 45;
}
method {:test} Test38() {
var r0 := CountEqualNumbers(46, 45, 45);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 46 == 45 && 45 == 45;
expect r0 == 2 <==> (46 == 45 && 45 != 45) || (46 != 45 && 45 == 45) || (46 == 45 && 45 != 45);
expect r0 == 1 <==> 46 != 45 && 45 != 45 && 46 != 45;
}
method {:test} Test39() {
var r0 := CountEqualNumbers(47, 46, 45);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 47 == 46 && 46 == 45;
expect r0 == 2 <==> (47 == 46 && 46 != 45) || (47 != 46 && 46 == 45) || (47 == 45 && 46 != 45);
expect r0 == 1 <==> 47 != 46 && 46 != 45 && 47 != 45;
}

// REPEAT 8 - TIME: 34.010099 s

method {:test} Test40() {
var r0 := CountEqualNumbers(48, 48, 48);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 48 == 48 && 48 == 48;
expect r0 == 2 <==> (48 == 48 && 48 != 48) || (48 != 48 && 48 == 48) || (48 == 48 && 48 != 48);
expect r0 == 1 <==> 48 != 48 && 48 != 48 && 48 != 48;
}
method {:test} Test41() {
var r0 := CountEqualNumbers(49, 49, 48);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 49 == 49 && 49 == 48;
expect r0 == 2 <==> (49 == 49 && 49 != 48) || (49 != 49 && 49 == 48) || (49 == 48 && 49 != 48);
expect r0 == 1 <==> 49 != 49 && 49 != 48 && 49 != 48;
}
method {:test} Test42() {
var r0 := CountEqualNumbers(48, 49, 48);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 48 == 49 && 49 == 48;
expect r0 == 2 <==> (48 == 49 && 49 != 48) || (48 != 49 && 49 == 48) || (48 == 48 && 49 != 48);
expect r0 == 1 <==> 48 != 49 && 49 != 48 && 48 != 48;
}
method {:test} Test43() {
var r0 := CountEqualNumbers(48, 49, 49);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 48 == 49 && 49 == 49;
expect r0 == 2 <==> (48 == 49 && 49 != 49) || (48 != 49 && 49 == 49) || (48 == 49 && 49 != 49);
expect r0 == 1 <==> 48 != 49 && 49 != 49 && 48 != 49;
}
method {:test} Test44() {
var r0 := CountEqualNumbers(48, 50, 49);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 48 == 50 && 50 == 49;
expect r0 == 2 <==> (48 == 50 && 50 != 49) || (48 != 50 && 50 == 49) || (48 == 49 && 50 != 49);
expect r0 == 1 <==> 48 != 50 && 50 != 49 && 48 != 49;
}

// REPEAT 9 - TIME: 39.0774522 s

method {:test} Test45() {
var r0 := CountEqualNumbers(51, 51, 51);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 51 == 51 && 51 == 51;
expect r0 == 2 <==> (51 == 51 && 51 != 51) || (51 != 51 && 51 == 51) || (51 == 51 && 51 != 51);
expect r0 == 1 <==> 51 != 51 && 51 != 51 && 51 != 51;
}
method {:test} Test46() {
var r0 := CountEqualNumbers(51, 51, 52);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 51 == 51 && 51 == 52;
expect r0 == 2 <==> (51 == 51 && 51 != 52) || (51 != 51 && 51 == 52) || (51 == 52 && 51 != 52);
expect r0 == 1 <==> 51 != 51 && 51 != 52 && 51 != 52;
}
method {:test} Test47() {
var r0 := CountEqualNumbers(52, 51, 52);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 52 == 51 && 51 == 52;
expect r0 == 2 <==> (52 == 51 && 51 != 52) || (52 != 51 && 51 == 52) || (52 == 52 && 51 != 52);
expect r0 == 1 <==> 52 != 51 && 51 != 52 && 52 != 52;
}
method {:test} Test48() {
var r0 := CountEqualNumbers(51, 52, 52);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 51 == 52 && 52 == 52;
expect r0 == 2 <==> (51 == 52 && 52 != 52) || (51 != 52 && 52 == 52) || (51 == 52 && 52 != 52);
expect r0 == 1 <==> 51 != 52 && 52 != 52 && 51 != 52;
}
method {:test} Test49() {
var r0 := CountEqualNumbers(52, 51, 53);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 52 == 51 && 51 == 53;
expect r0 == 2 <==> (52 == 51 && 51 != 53) || (52 != 51 && 51 == 53) || (52 == 53 && 51 != 53);
expect r0 == 1 <==> 52 != 51 && 51 != 53 && 52 != 53;
}

// REPEAT 10 - TIME: 43.9105422 s
