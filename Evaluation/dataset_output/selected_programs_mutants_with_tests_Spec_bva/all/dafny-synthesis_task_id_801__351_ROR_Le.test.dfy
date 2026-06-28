// dafny-synthesis_task_id_801.dfy

method {:testEntry} CountEqualNumbers(a: int, b: int, c: int)
    returns (count: int)
  ensures count >= 0 && count <= 3
  ensures count == 3 <==> a == b && b == c
  ensures count == 2 <==> (a == b && b != c) || (a != b && b == c) || (a == c && b != c)
  ensures count == 1 <==> a != b && b != c && a != c
{
  count := 1;
  if a <= b {
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
var r0 := CountEqualNumbers(25, 25, 25);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 25 == 25 && 25 == 25;
expect r0 == 2 <==> (25 == 25 && 25 != 25) || (25 != 25 && 25 == 25) || (25 == 25 && 25 != 25);
expect r0 == 1 <==> 25 != 25 && 25 != 25 && 25 != 25;
}
method {:test} Test1() {
var r0 := CountEqualNumbers(-100, -100, -100);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> -100 == -100 && -100 == -100;
expect r0 == 2 <==> (-100 == -100 && -100 != -100) || (-100 != -100 && -100 == -100) || (-100 == -100 && -100 != -100);
expect r0 == 1 <==> -100 != -100 && -100 != -100 && -100 != -100;
}
method {:test} Test2() {
var r0 := CountEqualNumbers(100, 100, 100);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 100 == 100 && 100 == 100;
expect r0 == 2 <==> (100 == 100 && 100 != 100) || (100 != 100 && 100 == 100) || (100 == 100 && 100 != 100);
expect r0 == 1 <==> 100 != 100 && 100 != 100 && 100 != 100;
}
method {:test} Test10() {
var r0 := CountEqualNumbers(26, 27, 27);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 26 == 27 && 27 == 27;
expect r0 == 2 <==> (26 == 27 && 27 != 27) || (26 != 27 && 27 == 27) || (26 == 27 && 27 != 27);
expect r0 == 1 <==> 26 != 27 && 27 != 27 && 26 != 27;
}
method {:test} Test11() {
var r0 := CountEqualNumbers(-100, 26, 26);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> -100 == 26 && 26 == 26;
expect r0 == 2 <==> (-100 == 26 && 26 != 26) || (-100 != 26 && 26 == 26) || (-100 == 26 && 26 != 26);
expect r0 == 1 <==> -100 != 26 && 26 != 26 && -100 != 26;
}
method {:test} Test12() {
var r0 := CountEqualNumbers(100, 26, 26);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 100 == 26 && 26 == 26;
expect r0 == 2 <==> (100 == 26 && 26 != 26) || (100 != 26 && 26 == 26) || (100 == 26 && 26 != 26);
expect r0 == 1 <==> 100 != 26 && 26 != 26 && 100 != 26;
}
method {:test} Test13() {
var r0 := CountEqualNumbers(26, -100, -100);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 26 == -100 && -100 == -100;
expect r0 == 2 <==> (26 == -100 && -100 != -100) || (26 != -100 && -100 == -100) || (26 == -100 && -100 != -100);
expect r0 == 1 <==> 26 != -100 && -100 != -100 && 26 != -100;
}
method {:test} Test14() {
var r0 := CountEqualNumbers(26, 100, 100);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 26 == 100 && 100 == 100;
expect r0 == 2 <==> (26 == 100 && 100 != 100) || (26 != 100 && 100 == 100) || (26 == 100 && 100 != 100);
expect r0 == 1 <==> 26 != 100 && 100 != 100 && 26 != 100;
}
method {:test} Test20() {
var r0 := CountEqualNumbers(27, 26, 27);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 27 == 26 && 26 == 27;
expect r0 == 2 <==> (27 == 26 && 26 != 27) || (27 != 26 && 26 == 27) || (27 == 27 && 26 != 27);
expect r0 == 1 <==> 27 != 26 && 26 != 27 && 27 != 27;
}
method {:test} Test21() {
var r0 := CountEqualNumbers(-100, 26, -100);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> -100 == 26 && 26 == -100;
expect r0 == 2 <==> (-100 == 26 && 26 != -100) || (-100 != 26 && 26 == -100) || (-100 == -100 && 26 != -100);
expect r0 == 1 <==> -100 != 26 && 26 != -100 && -100 != -100;
}
method {:test} Test22() {
var r0 := CountEqualNumbers(100, 26, 100);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 100 == 26 && 26 == 100;
expect r0 == 2 <==> (100 == 26 && 26 != 100) || (100 != 26 && 26 == 100) || (100 == 100 && 26 != 100);
expect r0 == 1 <==> 100 != 26 && 26 != 100 && 100 != 100;
}
method {:test} Test23() {
var r0 := CountEqualNumbers(26, -100, 26);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 26 == -100 && -100 == 26;
expect r0 == 2 <==> (26 == -100 && -100 != 26) || (26 != -100 && -100 == 26) || (26 == 26 && -100 != 26);
expect r0 == 1 <==> 26 != -100 && -100 != 26 && 26 != 26;
}
method {:test} Test24() {
var r0 := CountEqualNumbers(26, 100, 26);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 26 == 100 && 100 == 26;
expect r0 == 2 <==> (26 == 100 && 100 != 26) || (26 != 100 && 100 == 26) || (26 == 26 && 100 != 26);
expect r0 == 1 <==> 26 != 100 && 100 != 26 && 26 != 26;
}
method {:test} Test30() {
var r0 := CountEqualNumbers(26, 27, 28);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 26 == 27 && 27 == 28;
expect r0 == 2 <==> (26 == 27 && 27 != 28) || (26 != 27 && 27 == 28) || (26 == 28 && 27 != 28);
expect r0 == 1 <==> 26 != 27 && 27 != 28 && 26 != 28;
}
method {:test} Test31() {
var r0 := CountEqualNumbers(-100, 26, 27);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> -100 == 26 && 26 == 27;
expect r0 == 2 <==> (-100 == 26 && 26 != 27) || (-100 != 26 && 26 == 27) || (-100 == 27 && 26 != 27);
expect r0 == 1 <==> -100 != 26 && 26 != 27 && -100 != 27;
}
method {:test} Test32() {
var r0 := CountEqualNumbers(100, 26, 27);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 100 == 26 && 26 == 27;
expect r0 == 2 <==> (100 == 26 && 26 != 27) || (100 != 26 && 26 == 27) || (100 == 27 && 26 != 27);
expect r0 == 1 <==> 100 != 26 && 26 != 27 && 100 != 27;
}
method {:test} Test33() {
var r0 := CountEqualNumbers(26, -100, 27);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 26 == -100 && -100 == 27;
expect r0 == 2 <==> (26 == -100 && -100 != 27) || (26 != -100 && -100 == 27) || (26 == 27 && -100 != 27);
expect r0 == 1 <==> 26 != -100 && -100 != 27 && 26 != 27;
}
method {:test} Test34() {
var r0 := CountEqualNumbers(26, 100, 27);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 26 == 100 && 100 == 27;
expect r0 == 2 <==> (26 == 100 && 100 != 27) || (26 != 100 && 100 == 27) || (26 == 27 && 100 != 27);
expect r0 == 1 <==> 26 != 100 && 100 != 27 && 26 != 27;
}
method {:test} Test35() {
var r0 := CountEqualNumbers(26, 27, -100);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 26 == 27 && 27 == -100;
expect r0 == 2 <==> (26 == 27 && 27 != -100) || (26 != 27 && 27 == -100) || (26 == -100 && 27 != -100);
expect r0 == 1 <==> 26 != 27 && 27 != -100 && 26 != -100;
}
method {:test} Test36() {
var r0 := CountEqualNumbers(26, 27, 100);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 26 == 27 && 27 == 100;
expect r0 == 2 <==> (26 == 27 && 27 != 100) || (26 != 27 && 27 == 100) || (26 == 100 && 27 != 100);
expect r0 == 1 <==> 26 != 27 && 27 != 100 && 26 != 100;
}
method {:test} Test40() {
var r0 := CountEqualNumbers(26, 26, 27);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 26 == 26 && 26 == 27;
expect r0 == 2 <==> (26 == 26 && 26 != 27) || (26 != 26 && 26 == 27) || (26 == 27 && 26 != 27);
expect r0 == 1 <==> 26 != 26 && 26 != 27 && 26 != 27;
}
method {:test} Test41() {
var r0 := CountEqualNumbers(-100, -100, 26);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> -100 == -100 && -100 == 26;
expect r0 == 2 <==> (-100 == -100 && -100 != 26) || (-100 != -100 && -100 == 26) || (-100 == 26 && -100 != 26);
expect r0 == 1 <==> -100 != -100 && -100 != 26 && -100 != 26;
}
method {:test} Test42() {
var r0 := CountEqualNumbers(100, 100, 26);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 100 == 100 && 100 == 26;
expect r0 == 2 <==> (100 == 100 && 100 != 26) || (100 != 100 && 100 == 26) || (100 == 26 && 100 != 26);
expect r0 == 1 <==> 100 != 100 && 100 != 26 && 100 != 26;
}
method {:test} Test45() {
var r0 := CountEqualNumbers(26, 26, -100);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 26 == 26 && 26 == -100;
expect r0 == 2 <==> (26 == 26 && 26 != -100) || (26 != 26 && 26 == -100) || (26 == -100 && 26 != -100);
expect r0 == 1 <==> 26 != 26 && 26 != -100 && 26 != -100;
}
method {:test} Test46() {
var r0 := CountEqualNumbers(26, 26, 100);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 26 == 26 && 26 == 100;
expect r0 == 2 <==> (26 == 26 && 26 != 100) || (26 != 26 && 26 == 100) || (26 == 100 && 26 != 100);
expect r0 == 1 <==> 26 != 26 && 26 != 100 && 26 != 100;
}

// REPEAT 1 - TIME: 285.0170254 s

method {:test} Test50() {
var r0 := CountEqualNumbers(24, 24, 24);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 24 == 24 && 24 == 24;
expect r0 == 2 <==> (24 == 24 && 24 != 24) || (24 != 24 && 24 == 24) || (24 == 24 && 24 != 24);
expect r0 == 1 <==> 24 != 24 && 24 != 24 && 24 != 24;
}
method {:test} Test51() {
var r0 := CountEqualNumbers(30, 31, 31);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 30 == 31 && 31 == 31;
expect r0 == 2 <==> (30 == 31 && 31 != 31) || (30 != 31 && 31 == 31) || (30 == 31 && 31 != 31);
expect r0 == 1 <==> 30 != 31 && 31 != 31 && 30 != 31;
}
method {:test} Test52() {
var r0 := CountEqualNumbers(30, 31, 30);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 30 == 31 && 31 == 30;
expect r0 == 2 <==> (30 == 31 && 31 != 30) || (30 != 31 && 31 == 30) || (30 == 30 && 31 != 30);
expect r0 == 1 <==> 30 != 31 && 31 != 30 && 30 != 30;
}
method {:test} Test53() {
var r0 := CountEqualNumbers(30, 31, 32);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 30 == 31 && 31 == 32;
expect r0 == 2 <==> (30 == 31 && 31 != 32) || (30 != 31 && 31 == 32) || (30 == 32 && 31 != 32);
expect r0 == 1 <==> 30 != 31 && 31 != 32 && 30 != 32;
}
method {:test} Test54() {
var r0 := CountEqualNumbers(24, 24, 29);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 24 == 24 && 24 == 29;
expect r0 == 2 <==> (24 == 24 && 24 != 29) || (24 != 24 && 24 == 29) || (24 == 29 && 24 != 29);
expect r0 == 1 <==> 24 != 24 && 24 != 29 && 24 != 29;
}

// REPEAT 2 - TIME: 300.1486457 s

method {:test} Test55() {
var r0 := CountEqualNumbers(34, 34, 34);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 34 == 34 && 34 == 34;
expect r0 == 2 <==> (34 == 34 && 34 != 34) || (34 != 34 && 34 == 34) || (34 == 34 && 34 != 34);
expect r0 == 1 <==> 34 != 34 && 34 != 34 && 34 != 34;
}
method {:test} Test56() {
var r0 := CountEqualNumbers(34, 33, 33);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 34 == 33 && 33 == 33;
expect r0 == 2 <==> (34 == 33 && 33 != 33) || (34 != 33 && 33 == 33) || (34 == 33 && 33 != 33);
expect r0 == 1 <==> 34 != 33 && 33 != 33 && 34 != 33;
}
method {:test} Test57() {
var r0 := CountEqualNumbers(35, 36, 35);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 35 == 36 && 36 == 35;
expect r0 == 2 <==> (35 == 36 && 36 != 35) || (35 != 36 && 36 == 35) || (35 == 35 && 36 != 35);
expect r0 == 1 <==> 35 != 36 && 36 != 35 && 35 != 35;
}
method {:test} Test58() {
var r0 := CountEqualNumbers(34, 33, 35);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 34 == 33 && 33 == 35;
expect r0 == 2 <==> (34 == 33 && 33 != 35) || (34 != 33 && 33 == 35) || (34 == 35 && 33 != 35);
expect r0 == 1 <==> 34 != 33 && 33 != 35 && 34 != 35;
}
method {:test} Test59() {
var r0 := CountEqualNumbers(34, 34, 33);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 34 == 34 && 34 == 33;
expect r0 == 2 <==> (34 == 34 && 34 != 33) || (34 != 34 && 34 == 33) || (34 == 33 && 34 != 33);
expect r0 == 1 <==> 34 != 34 && 34 != 33 && 34 != 33;
}

// REPEAT 3 - TIME: 315.5266467 s

method {:test} Test60() {
var r0 := CountEqualNumbers(38, 38, 38);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 38 == 38 && 38 == 38;
expect r0 == 2 <==> (38 == 38 && 38 != 38) || (38 != 38 && 38 == 38) || (38 == 38 && 38 != 38);
expect r0 == 1 <==> 38 != 38 && 38 != 38 && 38 != 38;
}
method {:test} Test61() {
var r0 := CountEqualNumbers(38, 37, 37);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 38 == 37 && 37 == 37;
expect r0 == 2 <==> (38 == 37 && 37 != 37) || (38 != 37 && 37 == 37) || (38 == 37 && 37 != 37);
expect r0 == 1 <==> 38 != 37 && 37 != 37 && 38 != 37;
}
method {:test} Test62() {
var r0 := CountEqualNumbers(38, 37, 38);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 38 == 37 && 37 == 38;
expect r0 == 2 <==> (38 == 37 && 37 != 38) || (38 != 37 && 37 == 38) || (38 == 38 && 37 != 38);
expect r0 == 1 <==> 38 != 37 && 37 != 38 && 38 != 38;
}
method {:test} Test63() {
var r0 := CountEqualNumbers(39, 40, 41);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 39 == 40 && 40 == 41;
expect r0 == 2 <==> (39 == 40 && 40 != 41) || (39 != 40 && 40 == 41) || (39 == 41 && 40 != 41);
expect r0 == 1 <==> 39 != 40 && 40 != 41 && 39 != 41;
}
method {:test} Test64() {
var r0 := CountEqualNumbers(37, 37, 38);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 37 == 37 && 37 == 38;
expect r0 == 2 <==> (37 == 37 && 37 != 38) || (37 != 37 && 37 == 38) || (37 == 38 && 37 != 38);
expect r0 == 1 <==> 37 != 37 && 37 != 38 && 37 != 38;
}

// REPEAT 4 - TIME: 330.5759243 s

method {:test} Test65() {
var r0 := CountEqualNumbers(42, 42, 42);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 42 == 42 && 42 == 42;
expect r0 == 2 <==> (42 == 42 && 42 != 42) || (42 != 42 && 42 == 42) || (42 == 42 && 42 != 42);
expect r0 == 1 <==> 42 != 42 && 42 != 42 && 42 != 42;
}
method {:test} Test66() {
var r0 := CountEqualNumbers(43, 42, 42);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 43 == 42 && 42 == 42;
expect r0 == 2 <==> (43 == 42 && 42 != 42) || (43 != 42 && 42 == 42) || (43 == 42 && 42 != 42);
expect r0 == 1 <==> 43 != 42 && 42 != 42 && 43 != 42;
}
method {:test} Test67() {
var r0 := CountEqualNumbers(43, 42, 43);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 43 == 42 && 42 == 43;
expect r0 == 2 <==> (43 == 42 && 42 != 43) || (43 != 42 && 42 == 43) || (43 == 43 && 42 != 43);
expect r0 == 1 <==> 43 != 42 && 42 != 43 && 43 != 43;
}
method {:test} Test68() {
var r0 := CountEqualNumbers(43, 42, 44);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 43 == 42 && 42 == 44;
expect r0 == 2 <==> (43 == 42 && 42 != 44) || (43 != 42 && 42 == 44) || (43 == 44 && 42 != 44);
expect r0 == 1 <==> 43 != 42 && 42 != 44 && 43 != 44;
}
method {:test} Test69() {
var r0 := CountEqualNumbers(44, 44, 45);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 44 == 44 && 44 == 45;
expect r0 == 2 <==> (44 == 44 && 44 != 45) || (44 != 44 && 44 == 45) || (44 == 45 && 44 != 45);
expect r0 == 1 <==> 44 != 44 && 44 != 45 && 44 != 45;
}

// REPEAT 5 - TIME: 346.187416 s

method {:test} Test70() {
var r0 := CountEqualNumbers(46, 46, 46);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 46 == 46 && 46 == 46;
expect r0 == 2 <==> (46 == 46 && 46 != 46) || (46 != 46 && 46 == 46) || (46 == 46 && 46 != 46);
expect r0 == 1 <==> 46 != 46 && 46 != 46 && 46 != 46;
}
method {:test} Test71() {
var r0 := CountEqualNumbers(47, 46, 46);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 47 == 46 && 46 == 46;
expect r0 == 2 <==> (47 == 46 && 46 != 46) || (47 != 46 && 46 == 46) || (47 == 46 && 46 != 46);
expect r0 == 1 <==> 47 != 46 && 46 != 46 && 47 != 46;
}
method {:test} Test72() {
var r0 := CountEqualNumbers(48, 49, 48);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 48 == 49 && 49 == 48;
expect r0 == 2 <==> (48 == 49 && 49 != 48) || (48 != 49 && 49 == 48) || (48 == 48 && 49 != 48);
expect r0 == 1 <==> 48 != 49 && 49 != 48 && 48 != 48;
}
method {:test} Test73() {
var r0 := CountEqualNumbers(48, 49, 50);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 48 == 49 && 49 == 50;
expect r0 == 2 <==> (48 == 49 && 49 != 50) || (48 != 49 && 49 == 50) || (48 == 50 && 49 != 50);
expect r0 == 1 <==> 48 != 49 && 49 != 50 && 48 != 50;
}
method {:test} Test74() {
var r0 := CountEqualNumbers(47, 47, 46);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 47 == 47 && 47 == 46;
expect r0 == 2 <==> (47 == 47 && 47 != 46) || (47 != 47 && 47 == 46) || (47 == 46 && 47 != 46);
expect r0 == 1 <==> 47 != 47 && 47 != 46 && 47 != 46;
}

// REPEAT 6 - TIME: 361.2646717 s

method {:test} Test75() {
var r0 := CountEqualNumbers(51, 51, 51);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 51 == 51 && 51 == 51;
expect r0 == 2 <==> (51 == 51 && 51 != 51) || (51 != 51 && 51 == 51) || (51 == 51 && 51 != 51);
expect r0 == 1 <==> 51 != 51 && 51 != 51 && 51 != 51;
}
method {:test} Test76() {
var r0 := CountEqualNumbers(51, 52, 52);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 51 == 52 && 52 == 52;
expect r0 == 2 <==> (51 == 52 && 52 != 52) || (51 != 52 && 52 == 52) || (51 == 52 && 52 != 52);
expect r0 == 1 <==> 51 != 52 && 52 != 52 && 51 != 52;
}
method {:test} Test77() {
var r0 := CountEqualNumbers(53, 54, 53);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 53 == 54 && 54 == 53;
expect r0 == 2 <==> (53 == 54 && 54 != 53) || (53 != 54 && 54 == 53) || (53 == 53 && 54 != 53);
expect r0 == 1 <==> 53 != 54 && 54 != 53 && 53 != 53;
}
method {:test} Test78() {
var r0 := CountEqualNumbers(52, 51, 53);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 52 == 51 && 51 == 53;
expect r0 == 2 <==> (52 == 51 && 51 != 53) || (52 != 51 && 51 == 53) || (52 == 53 && 51 != 53);
expect r0 == 1 <==> 52 != 51 && 51 != 53 && 52 != 53;
}
method {:test} Test79() {
var r0 := CountEqualNumbers(51, 51, 52);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 51 == 51 && 51 == 52;
expect r0 == 2 <==> (51 == 51 && 51 != 52) || (51 != 51 && 51 == 52) || (51 == 52 && 51 != 52);
expect r0 == 1 <==> 51 != 51 && 51 != 52 && 51 != 52;
}

// REPEAT 7 - TIME: 376.2229756 s

method {:test} Test80() {
var r0 := CountEqualNumbers(55, 55, 55);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 55 == 55 && 55 == 55;
expect r0 == 2 <==> (55 == 55 && 55 != 55) || (55 != 55 && 55 == 55) || (55 == 55 && 55 != 55);
expect r0 == 1 <==> 55 != 55 && 55 != 55 && 55 != 55;
}
method {:test} Test81() {
var r0 := CountEqualNumbers(55, 56, 56);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 55 == 56 && 56 == 56;
expect r0 == 2 <==> (55 == 56 && 56 != 56) || (55 != 56 && 56 == 56) || (55 == 56 && 56 != 56);
expect r0 == 1 <==> 55 != 56 && 56 != 56 && 55 != 56;
}
method {:test} Test82() {
var r0 := CountEqualNumbers(56, 57, 56);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 56 == 57 && 57 == 56;
expect r0 == 2 <==> (56 == 57 && 57 != 56) || (56 != 57 && 57 == 56) || (56 == 56 && 57 != 56);
expect r0 == 1 <==> 56 != 57 && 57 != 56 && 56 != 56;
}
method {:test} Test83() {
var r0 := CountEqualNumbers(55, 57, 56);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 55 == 57 && 57 == 56;
expect r0 == 2 <==> (55 == 57 && 57 != 56) || (55 != 57 && 57 == 56) || (55 == 56 && 57 != 56);
expect r0 == 1 <==> 55 != 57 && 57 != 56 && 55 != 56;
}
method {:test} Test84() {
var r0 := CountEqualNumbers(55, 55, 56);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 55 == 55 && 55 == 56;
expect r0 == 2 <==> (55 == 55 && 55 != 56) || (55 != 55 && 55 == 56) || (55 == 56 && 55 != 56);
expect r0 == 1 <==> 55 != 55 && 55 != 56 && 55 != 56;
}

// REPEAT 8 - TIME: 389.464906 s

method {:test} Test85() {
var r0 := CountEqualNumbers(58, 58, 58);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 58 == 58 && 58 == 58;
expect r0 == 2 <==> (58 == 58 && 58 != 58) || (58 != 58 && 58 == 58) || (58 == 58 && 58 != 58);
expect r0 == 1 <==> 58 != 58 && 58 != 58 && 58 != 58;
}
method {:test} Test86() {
var r0 := CountEqualNumbers(59, 60, 60);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 59 == 60 && 60 == 60;
expect r0 == 2 <==> (59 == 60 && 60 != 60) || (59 != 60 && 60 == 60) || (59 == 60 && 60 != 60);
expect r0 == 1 <==> 59 != 60 && 60 != 60 && 59 != 60;
}
method {:test} Test87() {
var r0 := CountEqualNumbers(59, 60, 59);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 59 == 60 && 60 == 59;
expect r0 == 2 <==> (59 == 60 && 60 != 59) || (59 != 60 && 60 == 59) || (59 == 59 && 60 != 59);
expect r0 == 1 <==> 59 != 60 && 60 != 59 && 59 != 59;
}
method {:test} Test88() {
var r0 := CountEqualNumbers(59, 58, 60);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 59 == 58 && 58 == 60;
expect r0 == 2 <==> (59 == 58 && 58 != 60) || (59 != 58 && 58 == 60) || (59 == 60 && 58 != 60);
expect r0 == 1 <==> 59 != 58 && 58 != 60 && 59 != 60;
}
method {:test} Test89() {
var r0 := CountEqualNumbers(58, 58, 59);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 58 == 58 && 58 == 59;
expect r0 == 2 <==> (58 == 58 && 58 != 59) || (58 != 58 && 58 == 59) || (58 == 59 && 58 != 59);
expect r0 == 1 <==> 58 != 58 && 58 != 59 && 58 != 59;
}

// REPEAT 9 - TIME: 401.0085592 s

method {:test} Test90() {
var r0 := CountEqualNumbers(61, 61, 61);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 61 == 61 && 61 == 61;
expect r0 == 2 <==> (61 == 61 && 61 != 61) || (61 != 61 && 61 == 61) || (61 == 61 && 61 != 61);
expect r0 == 1 <==> 61 != 61 && 61 != 61 && 61 != 61;
}
method {:test} Test91() {
var r0 := CountEqualNumbers(62, 61, 61);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 62 == 61 && 61 == 61;
expect r0 == 2 <==> (62 == 61 && 61 != 61) || (62 != 61 && 61 == 61) || (62 == 61 && 61 != 61);
expect r0 == 1 <==> 62 != 61 && 61 != 61 && 62 != 61;
}
method {:test} Test92() {
var r0 := CountEqualNumbers(62, 61, 62);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 62 == 61 && 61 == 62;
expect r0 == 2 <==> (62 == 61 && 61 != 62) || (62 != 61 && 61 == 62) || (62 == 62 && 61 != 62);
expect r0 == 1 <==> 62 != 61 && 61 != 62 && 62 != 62;
}
method {:test} Test93() {
var r0 := CountEqualNumbers(61, 63, 62);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 61 == 63 && 63 == 62;
expect r0 == 2 <==> (61 == 63 && 63 != 62) || (61 != 63 && 63 == 62) || (61 == 62 && 63 != 62);
expect r0 == 1 <==> 61 != 63 && 63 != 62 && 61 != 62;
}
method {:test} Test94() {
var r0 := CountEqualNumbers(61, 61, 62);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 61 == 61 && 61 == 62;
expect r0 == 2 <==> (61 == 61 && 61 != 62) || (61 != 61 && 61 == 62) || (61 == 62 && 61 != 62);
expect r0 == 1 <==> 61 != 61 && 61 != 62 && 61 != 62;
}

// REPEAT 10 - TIME: 412.7115697 s
