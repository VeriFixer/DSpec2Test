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


method {:testEntry} CountEqualNumbers(a: int, b: int, c: int) returns (count: int)
    ensures count >= 0 && count <= 3
    ensures (count == 3) <==> (a == b && b == c)
    ensures (count == 2) <==> ((a == b && b != c) || (a != b && b == c) || (a == c && b != c))
    ensures (count == 1) <==> (a != b && b != c && a != c)
{
    count := 1;
    if (a == b) {
        count := count + 1;
    }
    if (a == c) {
        count := count + 1;
    }
    if (a != b && b == c) {
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

// REPEAT 1 - TIME: 24.1635394 s

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

// REPEAT 2 - TIME: 35.5020355 s

method {:test} Test10() {
var r0 := CountEqualNumbers(33, 33, 33);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 33 == 33 && 33 == 33;
expect r0 == 2 <==> (33 == 33 && 33 != 33) || (33 != 33 && 33 == 33) || (33 == 33 && 33 != 33);
expect r0 == 1 <==> 33 != 33 && 33 != 33 && 33 != 33;
}
method {:test} Test11() {
var r0 := CountEqualNumbers(34, 35, 35);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 34 == 35 && 35 == 35;
expect r0 == 2 <==> (34 == 35 && 35 != 35) || (34 != 35 && 35 == 35) || (34 == 35 && 35 != 35);
expect r0 == 1 <==> 34 != 35 && 35 != 35 && 34 != 35;
}
method {:test} Test12() {
var r0 := CountEqualNumbers(33, 24, 33);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 33 == 24 && 24 == 33;
expect r0 == 2 <==> (33 == 24 && 24 != 33) || (33 != 24 && 24 == 33) || (33 == 33 && 24 != 33);
expect r0 == 1 <==> 33 != 24 && 24 != 33 && 33 != 33;
}
method {:test} Test13() {
var r0 := CountEqualNumbers(33, 24, 34);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 33 == 24 && 24 == 34;
expect r0 == 2 <==> (33 == 24 && 24 != 34) || (33 != 24 && 24 == 34) || (33 == 34 && 24 != 34);
expect r0 == 1 <==> 33 != 24 && 24 != 34 && 33 != 34;
}
method {:test} Test14() {
var r0 := CountEqualNumbers(34, 34, 35);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 34 == 34 && 34 == 35;
expect r0 == 2 <==> (34 == 34 && 34 != 35) || (34 != 34 && 34 == 35) || (34 == 35 && 34 != 35);
expect r0 == 1 <==> 34 != 34 && 34 != 35 && 34 != 35;
}

// REPEAT 3 - TIME: 43.8805675 s

method {:test} Test15() {
var r0 := CountEqualNumbers(36, 36, 36);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 36 == 36 && 36 == 36;
expect r0 == 2 <==> (36 == 36 && 36 != 36) || (36 != 36 && 36 == 36) || (36 == 36 && 36 != 36);
expect r0 == 1 <==> 36 != 36 && 36 != 36 && 36 != 36;
}
method {:test} Test16() {
var r0 := CountEqualNumbers(37, 36, 36);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 37 == 36 && 36 == 36;
expect r0 == 2 <==> (37 == 36 && 36 != 36) || (37 != 36 && 36 == 36) || (37 == 36 && 36 != 36);
expect r0 == 1 <==> 37 != 36 && 36 != 36 && 37 != 36;
}
method {:test} Test17() {
var r0 := CountEqualNumbers(37, 36, 37);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 37 == 36 && 36 == 37;
expect r0 == 2 <==> (37 == 36 && 36 != 37) || (37 != 36 && 36 == 37) || (37 == 37 && 36 != 37);
expect r0 == 1 <==> 37 != 36 && 36 != 37 && 37 != 37;
}
method {:test} Test18() {
var r0 := CountEqualNumbers(38, 37, 36);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 38 == 37 && 37 == 36;
expect r0 == 2 <==> (38 == 37 && 37 != 36) || (38 != 37 && 37 == 36) || (38 == 36 && 37 != 36);
expect r0 == 1 <==> 38 != 37 && 37 != 36 && 38 != 36;
}
method {:test} Test19() {
var r0 := CountEqualNumbers(38, 38, 39);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 38 == 38 && 38 == 39;
expect r0 == 2 <==> (38 == 38 && 38 != 39) || (38 != 38 && 38 == 39) || (38 == 39 && 38 != 39);
expect r0 == 1 <==> 38 != 38 && 38 != 39 && 38 != 39;
}

// REPEAT 4 - TIME: 51.4317459 s

method {:test} Test20() {
var r0 := CountEqualNumbers(41, 41, 41);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 41 == 41 && 41 == 41;
expect r0 == 2 <==> (41 == 41 && 41 != 41) || (41 != 41 && 41 == 41) || (41 == 41 && 41 != 41);
expect r0 == 1 <==> 41 != 41 && 41 != 41 && 41 != 41;
}
method {:test} Test21() {
var r0 := CountEqualNumbers(41, 42, 42);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 41 == 42 && 42 == 42;
expect r0 == 2 <==> (41 == 42 && 42 != 42) || (41 != 42 && 42 == 42) || (41 == 42 && 42 != 42);
expect r0 == 1 <==> 41 != 42 && 42 != 42 && 41 != 42;
}
method {:test} Test22() {
var r0 := CountEqualNumbers(41, 42, 41);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 41 == 42 && 42 == 41;
expect r0 == 2 <==> (41 == 42 && 42 != 41) || (41 != 42 && 42 == 41) || (41 == 41 && 42 != 41);
expect r0 == 1 <==> 41 != 42 && 42 != 41 && 41 != 41;
}
method {:test} Test23() {
var r0 := CountEqualNumbers(42, 43, 40);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 42 == 43 && 43 == 40;
expect r0 == 2 <==> (42 == 43 && 43 != 40) || (42 != 43 && 43 == 40) || (42 == 40 && 43 != 40);
expect r0 == 1 <==> 42 != 43 && 43 != 40 && 42 != 40;
}
method {:test} Test24() {
var r0 := CountEqualNumbers(40, 40, 41);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 40 == 40 && 40 == 41;
expect r0 == 2 <==> (40 == 40 && 40 != 41) || (40 != 40 && 40 == 41) || (40 == 41 && 40 != 41);
expect r0 == 1 <==> 40 != 40 && 40 != 41 && 40 != 41;
}

// REPEAT 5 - TIME: 59.0973263 s

method {:test} Test25() {
var r0 := CountEqualNumbers(45, 45, 45);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 45 == 45 && 45 == 45;
expect r0 == 2 <==> (45 == 45 && 45 != 45) || (45 != 45 && 45 == 45) || (45 == 45 && 45 != 45);
expect r0 == 1 <==> 45 != 45 && 45 != 45 && 45 != 45;
}
method {:test} Test26() {
var r0 := CountEqualNumbers(45, 46, 46);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 45 == 46 && 46 == 46;
expect r0 == 2 <==> (45 == 46 && 46 != 46) || (45 != 46 && 46 == 46) || (45 == 46 && 46 != 46);
expect r0 == 1 <==> 45 != 46 && 46 != 46 && 45 != 46;
}
method {:test} Test27() {
var r0 := CountEqualNumbers(45, 44, 45);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 45 == 44 && 44 == 45;
expect r0 == 2 <==> (45 == 44 && 44 != 45) || (45 != 44 && 44 == 45) || (45 == 45 && 44 != 45);
expect r0 == 1 <==> 45 != 44 && 44 != 45 && 45 != 45;
}
method {:test} Test28() {
var r0 := CountEqualNumbers(45, 46, 47);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 45 == 46 && 46 == 47;
expect r0 == 2 <==> (45 == 46 && 46 != 47) || (45 != 46 && 46 == 47) || (45 == 47 && 46 != 47);
expect r0 == 1 <==> 45 != 46 && 46 != 47 && 45 != 47;
}
method {:test} Test29() {
var r0 := CountEqualNumbers(44, 44, 45);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 44 == 44 && 44 == 45;
expect r0 == 2 <==> (44 == 44 && 44 != 45) || (44 != 44 && 44 == 45) || (44 == 45 && 44 != 45);
expect r0 == 1 <==> 44 != 44 && 44 != 45 && 44 != 45;
}

// REPEAT 6 - TIME: 66.9517473 s

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
var r0 := CountEqualNumbers(49, 48, 49);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 49 == 48 && 48 == 49;
expect r0 == 2 <==> (49 == 48 && 48 != 49) || (49 != 48 && 48 == 49) || (49 == 49 && 48 != 49);
expect r0 == 1 <==> 49 != 48 && 48 != 49 && 49 != 49;
}
method {:test} Test33() {
var r0 := CountEqualNumbers(49, 48, 50);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 49 == 48 && 48 == 50;
expect r0 == 2 <==> (49 == 48 && 48 != 50) || (49 != 48 && 48 == 50) || (49 == 50 && 48 != 50);
expect r0 == 1 <==> 49 != 48 && 48 != 50 && 49 != 50;
}
method {:test} Test34() {
var r0 := CountEqualNumbers(50, 50, 51);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 50 == 50 && 50 == 51;
expect r0 == 2 <==> (50 == 50 && 50 != 51) || (50 != 50 && 50 == 51) || (50 == 51 && 50 != 51);
expect r0 == 1 <==> 50 != 50 && 50 != 51 && 50 != 51;
}

// REPEAT 7 - TIME: 74.6650876 s

method {:test} Test35() {
var r0 := CountEqualNumbers(52, 52, 52);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 52 == 52 && 52 == 52;
expect r0 == 2 <==> (52 == 52 && 52 != 52) || (52 != 52 && 52 == 52) || (52 == 52 && 52 != 52);
expect r0 == 1 <==> 52 != 52 && 52 != 52 && 52 != 52;
}
method {:test} Test36() {
var r0 := CountEqualNumbers(53, 52, 52);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 53 == 52 && 52 == 52;
expect r0 == 2 <==> (53 == 52 && 52 != 52) || (53 != 52 && 52 == 52) || (53 == 52 && 52 != 52);
expect r0 == 1 <==> 53 != 52 && 52 != 52 && 53 != 52;
}
method {:test} Test37() {
var r0 := CountEqualNumbers(53, 54, 53);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 53 == 54 && 54 == 53;
expect r0 == 2 <==> (53 == 54 && 54 != 53) || (53 != 54 && 54 == 53) || (53 == 53 && 54 != 53);
expect r0 == 1 <==> 53 != 54 && 54 != 53 && 53 != 53;
}
method {:test} Test38() {
var r0 := CountEqualNumbers(53, 54, 55);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 53 == 54 && 54 == 55;
expect r0 == 2 <==> (53 == 54 && 54 != 55) || (53 != 54 && 54 == 55) || (53 == 55 && 54 != 55);
expect r0 == 1 <==> 53 != 54 && 54 != 55 && 53 != 55;
}
method {:test} Test39() {
var r0 := CountEqualNumbers(52, 52, 53);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 52 == 52 && 52 == 53;
expect r0 == 2 <==> (52 == 52 && 52 != 53) || (52 != 52 && 52 == 53) || (52 == 53 && 52 != 53);
expect r0 == 1 <==> 52 != 52 && 52 != 53 && 52 != 53;
}

// REPEAT 8 - TIME: 82.3728346 s

method {:test} Test40() {
var r0 := CountEqualNumbers(57, 57, 57);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 57 == 57 && 57 == 57;
expect r0 == 2 <==> (57 == 57 && 57 != 57) || (57 != 57 && 57 == 57) || (57 == 57 && 57 != 57);
expect r0 == 1 <==> 57 != 57 && 57 != 57 && 57 != 57;
}
method {:test} Test41() {
var r0 := CountEqualNumbers(57, 56, 56);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 57 == 56 && 56 == 56;
expect r0 == 2 <==> (57 == 56 && 56 != 56) || (57 != 56 && 56 == 56) || (57 == 56 && 56 != 56);
expect r0 == 1 <==> 57 != 56 && 56 != 56 && 57 != 56;
}
method {:test} Test42() {
var r0 := CountEqualNumbers(58, 59, 58);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 58 == 59 && 59 == 58;
expect r0 == 2 <==> (58 == 59 && 59 != 58) || (58 != 59 && 59 == 58) || (58 == 58 && 59 != 58);
expect r0 == 1 <==> 58 != 59 && 59 != 58 && 58 != 58;
}
method {:test} Test43() {
var r0 := CountEqualNumbers(57, 56, 58);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 57 == 56 && 56 == 58;
expect r0 == 2 <==> (57 == 56 && 56 != 58) || (57 != 56 && 56 == 58) || (57 == 58 && 56 != 58);
expect r0 == 1 <==> 57 != 56 && 56 != 58 && 57 != 58;
}
method {:test} Test44() {
var r0 := CountEqualNumbers(57, 57, 56);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 57 == 57 && 57 == 56;
expect r0 == 2 <==> (57 == 57 && 57 != 56) || (57 != 57 && 57 == 56) || (57 == 56 && 57 != 56);
expect r0 == 1 <==> 57 != 57 && 57 != 56 && 57 != 56;
}

// REPEAT 9 - TIME: 90.2612501 s

method {:test} Test45() {
var r0 := CountEqualNumbers(60, 60, 60);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 60 == 60 && 60 == 60;
expect r0 == 2 <==> (60 == 60 && 60 != 60) || (60 != 60 && 60 == 60) || (60 == 60 && 60 != 60);
expect r0 == 1 <==> 60 != 60 && 60 != 60 && 60 != 60;
}
method {:test} Test46() {
var r0 := CountEqualNumbers(61, 60, 60);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 61 == 60 && 60 == 60;
expect r0 == 2 <==> (61 == 60 && 60 != 60) || (61 != 60 && 60 == 60) || (61 == 60 && 60 != 60);
expect r0 == 1 <==> 61 != 60 && 60 != 60 && 61 != 60;
}
method {:test} Test47() {
var r0 := CountEqualNumbers(61, 60, 61);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 61 == 60 && 60 == 61;
expect r0 == 2 <==> (61 == 60 && 60 != 61) || (61 != 60 && 60 == 61) || (61 == 61 && 60 != 61);
expect r0 == 1 <==> 61 != 60 && 60 != 61 && 61 != 61;
}
method {:test} Test48() {
var r0 := CountEqualNumbers(62, 61, 60);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 62 == 61 && 61 == 60;
expect r0 == 2 <==> (62 == 61 && 61 != 60) || (62 != 61 && 61 == 60) || (62 == 60 && 61 != 60);
expect r0 == 1 <==> 62 != 61 && 61 != 60 && 62 != 60;
}
method {:test} Test49() {
var r0 := CountEqualNumbers(60, 60, 61);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 60 == 60 && 60 == 61;
expect r0 == 2 <==> (60 == 60 && 60 != 61) || (60 != 60 && 60 == 61) || (60 == 61 && 60 != 61);
expect r0 == 1 <==> 60 != 60 && 60 != 61 && 60 != 61;
}

// REPEAT 10 - TIME: 98.0844324 s
