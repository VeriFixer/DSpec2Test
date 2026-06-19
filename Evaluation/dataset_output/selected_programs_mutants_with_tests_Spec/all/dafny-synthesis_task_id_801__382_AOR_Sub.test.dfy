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
    count := count - 1;
  }
  if a == c {
    count := count + 1;
  }
  if a != b && b == c {
    count := count + 1;
  }
}


method {:test} Test0() {
var r0 := CountEqualNumbers(25, 25, 25);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 25 == 25 && 25 == 25;
expect r0 == 2 <==> (25 == 25 && 25 != 25) || (25 != 25 && 25 == 25) || (25 == 25 && 25 != 25);
expect r0 == 1 <==> 25 != 25 && 25 != 25 && 25 != 25;
}
method {:test} Test1() {
var r0 := CountEqualNumbers(26, 27, 27);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 26 == 27 && 27 == 27;
expect r0 == 2 <==> (26 == 27 && 27 != 27) || (26 != 27 && 27 == 27) || (26 == 27 && 27 != 27);
expect r0 == 1 <==> 26 != 27 && 27 != 27 && 26 != 27;
}
method {:test} Test2() {
var r0 := CountEqualNumbers(27, 26, 27);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 27 == 26 && 26 == 27;
expect r0 == 2 <==> (27 == 26 && 26 != 27) || (27 != 26 && 26 == 27) || (27 == 27 && 26 != 27);
expect r0 == 1 <==> 27 != 26 && 26 != 27 && 27 != 27;
}
method {:test} Test3() {
var r0 := CountEqualNumbers(26, 27, 28);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 26 == 27 && 27 == 28;
expect r0 == 2 <==> (26 == 27 && 27 != 28) || (26 != 27 && 27 == 28) || (26 == 28 && 27 != 28);
expect r0 == 1 <==> 26 != 27 && 27 != 28 && 26 != 28;
}
method {:test} Test4() {
var r0 := CountEqualNumbers(26, 26, 27);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 26 == 26 && 26 == 27;
expect r0 == 2 <==> (26 == 26 && 26 != 27) || (26 != 26 && 26 == 27) || (26 == 27 && 26 != 27);
expect r0 == 1 <==> 26 != 26 && 26 != 27 && 26 != 27;
}

// REPEAT 1 - TIME: 25.8358706 s

method {:test} Test5() {
var r0 := CountEqualNumbers(29, 29, 29);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 29 == 29 && 29 == 29;
expect r0 == 2 <==> (29 == 29 && 29 != 29) || (29 != 29 && 29 == 29) || (29 == 29 && 29 != 29);
expect r0 == 1 <==> 29 != 29 && 29 != 29 && 29 != 29;
}
method {:test} Test6() {
var r0 := CountEqualNumbers(30, 31, 31);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 30 == 31 && 31 == 31;
expect r0 == 2 <==> (30 == 31 && 31 != 31) || (30 != 31 && 31 == 31) || (30 == 31 && 31 != 31);
expect r0 == 1 <==> 30 != 31 && 31 != 31 && 30 != 31;
}
method {:test} Test7() {
var r0 := CountEqualNumbers(30, 31, 30);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 30 == 31 && 31 == 30;
expect r0 == 2 <==> (30 == 31 && 31 != 30) || (30 != 31 && 31 == 30) || (30 == 30 && 31 != 30);
expect r0 == 1 <==> 30 != 31 && 31 != 30 && 30 != 30;
}
method {:test} Test8() {
var r0 := CountEqualNumbers(30, 31, 32);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 30 == 31 && 31 == 32;
expect r0 == 2 <==> (30 == 31 && 31 != 32) || (30 != 31 && 31 == 32) || (30 == 32 && 31 != 32);
expect r0 == 1 <==> 30 != 31 && 31 != 32 && 30 != 32;
}
method {:test} Test9() {
var r0 := CountEqualNumbers(30, 30, 31);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 30 == 30 && 30 == 31;
expect r0 == 2 <==> (30 == 30 && 30 != 31) || (30 != 30 && 30 == 31) || (30 == 31 && 30 != 31);
expect r0 == 1 <==> 30 != 30 && 30 != 31 && 30 != 31;
}

// REPEAT 2 - TIME: 41.4494884 s

method {:test} Test10() {
var r0 := CountEqualNumbers(24, 24, 24);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 24 == 24 && 24 == 24;
expect r0 == 2 <==> (24 == 24 && 24 != 24) || (24 != 24 && 24 == 24) || (24 == 24 && 24 != 24);
expect r0 == 1 <==> 24 != 24 && 24 != 24 && 24 != 24;
}
method {:test} Test11() {
var r0 := CountEqualNumbers(34, 35, 35);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 34 == 35 && 35 == 35;
expect r0 == 2 <==> (34 == 35 && 35 != 35) || (34 != 35 && 35 == 35) || (34 == 35 && 35 != 35);
expect r0 == 1 <==> 34 != 35 && 35 != 35 && 34 != 35;
}
method {:test} Test12() {
var r0 := CountEqualNumbers(34, 35, 34);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 34 == 35 && 35 == 34;
expect r0 == 2 <==> (34 == 35 && 35 != 34) || (34 != 35 && 35 == 34) || (34 == 34 && 35 != 34);
expect r0 == 1 <==> 34 != 35 && 35 != 34 && 34 != 34;
}
method {:test} Test13() {
var r0 := CountEqualNumbers(35, 36, 24);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 35 == 36 && 36 == 24;
expect r0 == 2 <==> (35 == 36 && 36 != 24) || (35 != 36 && 36 == 24) || (35 == 24 && 36 != 24);
expect r0 == 1 <==> 35 != 36 && 36 != 24 && 35 != 24;
}
method {:test} Test14() {
var r0 := CountEqualNumbers(24, 24, 33);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 24 == 24 && 24 == 33;
expect r0 == 2 <==> (24 == 24 && 24 != 33) || (24 != 24 && 24 == 33) || (24 == 33 && 24 != 33);
expect r0 == 1 <==> 24 != 24 && 24 != 33 && 24 != 33;
}

// REPEAT 3 - TIME: 49.3561452 s

method {:test} Test15() {
var r0 := CountEqualNumbers(38, 38, 38);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 38 == 38 && 38 == 38;
expect r0 == 2 <==> (38 == 38 && 38 != 38) || (38 != 38 && 38 == 38) || (38 == 38 && 38 != 38);
expect r0 == 1 <==> 38 != 38 && 38 != 38 && 38 != 38;
}
method {:test} Test16() {
var r0 := CountEqualNumbers(39, 40, 40);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 39 == 40 && 40 == 40;
expect r0 == 2 <==> (39 == 40 && 40 != 40) || (39 != 40 && 40 == 40) || (39 == 40 && 40 != 40);
expect r0 == 1 <==> 39 != 40 && 40 != 40 && 39 != 40;
}
method {:test} Test17() {
var r0 := CountEqualNumbers(38, 37, 38);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 38 == 37 && 37 == 38;
expect r0 == 2 <==> (38 == 37 && 37 != 38) || (38 != 37 && 37 == 38) || (38 == 38 && 37 != 38);
expect r0 == 1 <==> 38 != 37 && 37 != 38 && 38 != 38;
}
method {:test} Test18() {
var r0 := CountEqualNumbers(38, 37, 39);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 38 == 37 && 37 == 39;
expect r0 == 2 <==> (38 == 37 && 37 != 39) || (38 != 37 && 37 == 39) || (38 == 39 && 37 != 39);
expect r0 == 1 <==> 38 != 37 && 37 != 39 && 38 != 39;
}
method {:test} Test19() {
var r0 := CountEqualNumbers(39, 39, 40);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 39 == 39 && 39 == 40;
expect r0 == 2 <==> (39 == 39 && 39 != 40) || (39 != 39 && 39 == 40) || (39 == 40 && 39 != 40);
expect r0 == 1 <==> 39 != 39 && 39 != 40 && 39 != 40;
}

// REPEAT 4 - TIME: 57.1943405 s

method {:test} Test20() {
var r0 := CountEqualNumbers(42, 42, 42);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 42 == 42 && 42 == 42;
expect r0 == 2 <==> (42 == 42 && 42 != 42) || (42 != 42 && 42 == 42) || (42 == 42 && 42 != 42);
expect r0 == 1 <==> 42 != 42 && 42 != 42 && 42 != 42;
}
method {:test} Test21() {
var r0 := CountEqualNumbers(42, 43, 43);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 42 == 43 && 43 == 43;
expect r0 == 2 <==> (42 == 43 && 43 != 43) || (42 != 43 && 43 == 43) || (42 == 43 && 43 != 43);
expect r0 == 1 <==> 42 != 43 && 43 != 43 && 42 != 43;
}
method {:test} Test22() {
var r0 := CountEqualNumbers(42, 41, 42);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 42 == 41 && 41 == 42;
expect r0 == 2 <==> (42 == 41 && 41 != 42) || (42 != 41 && 41 == 42) || (42 == 42 && 41 != 42);
expect r0 == 1 <==> 42 != 41 && 41 != 42 && 42 != 42;
}
method {:test} Test23() {
var r0 := CountEqualNumbers(43, 42, 41);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 43 == 42 && 42 == 41;
expect r0 == 2 <==> (43 == 42 && 42 != 41) || (43 != 42 && 42 == 41) || (43 == 41 && 42 != 41);
expect r0 == 1 <==> 43 != 42 && 42 != 41 && 43 != 41;
}
method {:test} Test24() {
var r0 := CountEqualNumbers(42, 42, 43);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 42 == 42 && 42 == 43;
expect r0 == 2 <==> (42 == 42 && 42 != 43) || (42 != 42 && 42 == 43) || (42 == 43 && 42 != 43);
expect r0 == 1 <==> 42 != 42 && 42 != 43 && 42 != 43;
}

// REPEAT 5 - TIME: 65.1123899 s

method {:test} Test25() {
var r0 := CountEqualNumbers(44, 44, 44);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 44 == 44 && 44 == 44;
expect r0 == 2 <==> (44 == 44 && 44 != 44) || (44 != 44 && 44 == 44) || (44 == 44 && 44 != 44);
expect r0 == 1 <==> 44 != 44 && 44 != 44 && 44 != 44;
}
method {:test} Test26() {
var r0 := CountEqualNumbers(45, 44, 44);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 45 == 44 && 44 == 44;
expect r0 == 2 <==> (45 == 44 && 44 != 44) || (45 != 44 && 44 == 44) || (45 == 44 && 44 != 44);
expect r0 == 1 <==> 45 != 44 && 44 != 44 && 45 != 44;
}
method {:test} Test27() {
var r0 := CountEqualNumbers(46, 47, 46);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 46 == 47 && 47 == 46;
expect r0 == 2 <==> (46 == 47 && 47 != 46) || (46 != 47 && 47 == 46) || (46 == 46 && 47 != 46);
expect r0 == 1 <==> 46 != 47 && 47 != 46 && 46 != 46;
}
method {:test} Test28() {
var r0 := CountEqualNumbers(45, 44, 46);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 45 == 44 && 44 == 46;
expect r0 == 2 <==> (45 == 44 && 44 != 46) || (45 != 44 && 44 == 46) || (45 == 46 && 44 != 46);
expect r0 == 1 <==> 45 != 44 && 44 != 46 && 45 != 46;
}
method {:test} Test29() {
var r0 := CountEqualNumbers(46, 46, 47);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 46 == 46 && 46 == 47;
expect r0 == 2 <==> (46 == 46 && 46 != 47) || (46 != 46 && 46 == 47) || (46 == 47 && 46 != 47);
expect r0 == 1 <==> 46 != 46 && 46 != 47 && 46 != 47;
}

// REPEAT 6 - TIME: 73.080445 s

method {:test} Test30() {
var r0 := CountEqualNumbers(48, 48, 48);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 48 == 48 && 48 == 48;
expect r0 == 2 <==> (48 == 48 && 48 != 48) || (48 != 48 && 48 == 48) || (48 == 48 && 48 != 48);
expect r0 == 1 <==> 48 != 48 && 48 != 48 && 48 != 48;
}
method {:test} Test31() {
var r0 := CountEqualNumbers(50, 51, 51);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 50 == 51 && 51 == 51;
expect r0 == 2 <==> (50 == 51 && 51 != 51) || (50 != 51 && 51 == 51) || (50 == 51 && 51 != 51);
expect r0 == 1 <==> 50 != 51 && 51 != 51 && 50 != 51;
}
method {:test} Test32() {
var r0 := CountEqualNumbers(50, 51, 50);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 50 == 51 && 51 == 50;
expect r0 == 2 <==> (50 == 51 && 51 != 50) || (50 != 51 && 51 == 50) || (50 == 50 && 51 != 50);
expect r0 == 1 <==> 50 != 51 && 51 != 50 && 50 != 50;
}
method {:test} Test33() {
var r0 := CountEqualNumbers(50, 51, 52);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 50 == 51 && 51 == 52;
expect r0 == 2 <==> (50 == 51 && 51 != 52) || (50 != 51 && 51 == 52) || (50 == 52 && 51 != 52);
expect r0 == 1 <==> 50 != 51 && 51 != 52 && 50 != 52;
}
method {:test} Test34() {
var r0 := CountEqualNumbers(49, 49, 48);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 49 == 49 && 49 == 48;
expect r0 == 2 <==> (49 == 49 && 49 != 48) || (49 != 49 && 49 == 48) || (49 == 48 && 49 != 48);
expect r0 == 1 <==> 49 != 49 && 49 != 48 && 49 != 48;
}

// REPEAT 7 - TIME: 81.173405 s

method {:test} Test35() {
var r0 := CountEqualNumbers(53, 53, 53);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 53 == 53 && 53 == 53;
expect r0 == 2 <==> (53 == 53 && 53 != 53) || (53 != 53 && 53 == 53) || (53 == 53 && 53 != 53);
expect r0 == 1 <==> 53 != 53 && 53 != 53 && 53 != 53;
}
method {:test} Test36() {
var r0 := CountEqualNumbers(54, 53, 53);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 54 == 53 && 53 == 53;
expect r0 == 2 <==> (54 == 53 && 53 != 53) || (54 != 53 && 53 == 53) || (54 == 53 && 53 != 53);
expect r0 == 1 <==> 54 != 53 && 53 != 53 && 54 != 53;
}
method {:test} Test37() {
var r0 := CountEqualNumbers(54, 55, 54);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 54 == 55 && 55 == 54;
expect r0 == 2 <==> (54 == 55 && 55 != 54) || (54 != 55 && 55 == 54) || (54 == 54 && 55 != 54);
expect r0 == 1 <==> 54 != 55 && 55 != 54 && 54 != 54;
}
method {:test} Test38() {
var r0 := CountEqualNumbers(54, 55, 56);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 54 == 55 && 55 == 56;
expect r0 == 2 <==> (54 == 55 && 55 != 56) || (54 != 55 && 55 == 56) || (54 == 56 && 55 != 56);
expect r0 == 1 <==> 54 != 55 && 55 != 56 && 54 != 56;
}
method {:test} Test39() {
var r0 := CountEqualNumbers(53, 53, 54);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 53 == 53 && 53 == 54;
expect r0 == 2 <==> (53 == 53 && 53 != 54) || (53 != 53 && 53 == 54) || (53 == 54 && 53 != 54);
expect r0 == 1 <==> 53 != 53 && 53 != 54 && 53 != 54;
}

// REPEAT 8 - TIME: 89.3777646 s

method {:test} Test40() {
var r0 := CountEqualNumbers(58, 58, 58);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 58 == 58 && 58 == 58;
expect r0 == 2 <==> (58 == 58 && 58 != 58) || (58 != 58 && 58 == 58) || (58 == 58 && 58 != 58);
expect r0 == 1 <==> 58 != 58 && 58 != 58 && 58 != 58;
}
method {:test} Test41() {
var r0 := CountEqualNumbers(58, 57, 57);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 58 == 57 && 57 == 57;
expect r0 == 2 <==> (58 == 57 && 57 != 57) || (58 != 57 && 57 == 57) || (58 == 57 && 57 != 57);
expect r0 == 1 <==> 58 != 57 && 57 != 57 && 58 != 57;
}
method {:test} Test42() {
var r0 := CountEqualNumbers(59, 60, 59);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 59 == 60 && 60 == 59;
expect r0 == 2 <==> (59 == 60 && 60 != 59) || (59 != 60 && 60 == 59) || (59 == 59 && 60 != 59);
expect r0 == 1 <==> 59 != 60 && 60 != 59 && 59 != 59;
}
method {:test} Test43() {
var r0 := CountEqualNumbers(58, 57, 59);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 58 == 57 && 57 == 59;
expect r0 == 2 <==> (58 == 57 && 57 != 59) || (58 != 57 && 57 == 59) || (58 == 59 && 57 != 59);
expect r0 == 1 <==> 58 != 57 && 57 != 59 && 58 != 59;
}
method {:test} Test44() {
var r0 := CountEqualNumbers(58, 58, 57);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 58 == 58 && 58 == 57;
expect r0 == 2 <==> (58 == 58 && 58 != 57) || (58 != 58 && 58 == 57) || (58 == 57 && 58 != 57);
expect r0 == 1 <==> 58 != 58 && 58 != 57 && 58 != 57;
}

// REPEAT 9 - TIME: 97.6618945 s

method {:test} Test45() {
var r0 := CountEqualNumbers(61, 61, 61);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 61 == 61 && 61 == 61;
expect r0 == 2 <==> (61 == 61 && 61 != 61) || (61 != 61 && 61 == 61) || (61 == 61 && 61 != 61);
expect r0 == 1 <==> 61 != 61 && 61 != 61 && 61 != 61;
}
method {:test} Test46() {
var r0 := CountEqualNumbers(62, 61, 61);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 62 == 61 && 61 == 61;
expect r0 == 2 <==> (62 == 61 && 61 != 61) || (62 != 61 && 61 == 61) || (62 == 61 && 61 != 61);
expect r0 == 1 <==> 62 != 61 && 61 != 61 && 62 != 61;
}
method {:test} Test47() {
var r0 := CountEqualNumbers(62, 61, 62);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 62 == 61 && 61 == 62;
expect r0 == 2 <==> (62 == 61 && 61 != 62) || (62 != 61 && 61 == 62) || (62 == 62 && 61 != 62);
expect r0 == 1 <==> 62 != 61 && 61 != 62 && 62 != 62;
}
method {:test} Test48() {
var r0 := CountEqualNumbers(63, 62, 61);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 63 == 62 && 62 == 61;
expect r0 == 2 <==> (63 == 62 && 62 != 61) || (63 != 62 && 62 == 61) || (63 == 61 && 62 != 61);
expect r0 == 1 <==> 63 != 62 && 62 != 61 && 63 != 61;
}
method {:test} Test49() {
var r0 := CountEqualNumbers(61, 61, 62);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 61 == 61 && 61 == 62;
expect r0 == 2 <==> (61 == 61 && 61 != 62) || (61 != 61 && 61 == 62) || (61 == 62 && 61 != 62);
expect r0 == 1 <==> 61 != 61 && 61 != 62 && 61 != 62;
}

// REPEAT 10 - TIME: 105.6417084 s
