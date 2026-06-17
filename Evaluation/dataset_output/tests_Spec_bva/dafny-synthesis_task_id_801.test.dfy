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

// REPEAT 1 - TIME: 119.7965071 s

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

// REPEAT 2 - TIME: 127.5341762 s

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
var r0 := CountEqualNumbers(34, 35, 34);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 34 == 35 && 35 == 34;
expect r0 == 2 <==> (34 == 35 && 35 != 34) || (34 != 35 && 35 == 34) || (34 == 34 && 35 != 34);
expect r0 == 1 <==> 34 != 35 && 35 != 34 && 34 != 34;
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

// REPEAT 3 - TIME: 135.3213361 s

method {:test} Test60() {
var r0 := CountEqualNumbers(37, 37, 37);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 37 == 37 && 37 == 37;
expect r0 == 2 <==> (37 == 37 && 37 != 37) || (37 != 37 && 37 == 37) || (37 == 37 && 37 != 37);
expect r0 == 1 <==> 37 != 37 && 37 != 37 && 37 != 37;
}
method {:test} Test61() {
var r0 := CountEqualNumbers(38, 39, 39);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 38 == 39 && 39 == 39;
expect r0 == 2 <==> (38 == 39 && 39 != 39) || (38 != 39 && 39 == 39) || (38 == 39 && 39 != 39);
expect r0 == 1 <==> 38 != 39 && 39 != 39 && 38 != 39;
}
method {:test} Test62() {
var r0 := CountEqualNumbers(37, 36, 37);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 37 == 36 && 36 == 37;
expect r0 == 2 <==> (37 == 36 && 36 != 37) || (37 != 36 && 36 == 37) || (37 == 37 && 36 != 37);
expect r0 == 1 <==> 37 != 36 && 36 != 37 && 37 != 37;
}
method {:test} Test63() {
var r0 := CountEqualNumbers(38, 39, 40);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 38 == 39 && 39 == 40;
expect r0 == 2 <==> (38 == 39 && 39 != 40) || (38 != 39 && 39 == 40) || (38 == 40 && 39 != 40);
expect r0 == 1 <==> 38 != 39 && 39 != 40 && 38 != 40;
}
method {:test} Test64() {
var r0 := CountEqualNumbers(36, 36, 37);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 36 == 36 && 36 == 37;
expect r0 == 2 <==> (36 == 36 && 36 != 37) || (36 != 36 && 36 == 37) || (36 == 37 && 36 != 37);
expect r0 == 1 <==> 36 != 36 && 36 != 37 && 36 != 37;
}

// REPEAT 4 - TIME: 143.046611 s

method {:test} Test65() {
var r0 := CountEqualNumbers(41, 41, 41);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 41 == 41 && 41 == 41;
expect r0 == 2 <==> (41 == 41 && 41 != 41) || (41 != 41 && 41 == 41) || (41 == 41 && 41 != 41);
expect r0 == 1 <==> 41 != 41 && 41 != 41 && 41 != 41;
}
method {:test} Test66() {
var r0 := CountEqualNumbers(43, 44, 44);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 43 == 44 && 44 == 44;
expect r0 == 2 <==> (43 == 44 && 44 != 44) || (43 != 44 && 44 == 44) || (43 == 44 && 44 != 44);
expect r0 == 1 <==> 43 != 44 && 44 != 44 && 43 != 44;
}
method {:test} Test67() {
var r0 := CountEqualNumbers(41, 42, 41);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 41 == 42 && 42 == 41;
expect r0 == 2 <==> (41 == 42 && 42 != 41) || (41 != 42 && 42 == 41) || (41 == 41 && 42 != 41);
expect r0 == 1 <==> 41 != 42 && 42 != 41 && 41 != 41;
}
method {:test} Test68() {
var r0 := CountEqualNumbers(42, 43, 41);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 42 == 43 && 43 == 41;
expect r0 == 2 <==> (42 == 43 && 43 != 41) || (42 != 43 && 43 == 41) || (42 == 41 && 43 != 41);
expect r0 == 1 <==> 42 != 43 && 43 != 41 && 42 != 41;
}
method {:test} Test69() {
var r0 := CountEqualNumbers(43, 43, 44);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 43 == 43 && 43 == 44;
expect r0 == 2 <==> (43 == 43 && 43 != 44) || (43 != 43 && 43 == 44) || (43 == 44 && 43 != 44);
expect r0 == 1 <==> 43 != 43 && 43 != 44 && 43 != 44;
}

// REPEAT 5 - TIME: 150.5592271 s

method {:test} Test70() {
var r0 := CountEqualNumbers(45, 45, 45);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 45 == 45 && 45 == 45;
expect r0 == 2 <==> (45 == 45 && 45 != 45) || (45 != 45 && 45 == 45) || (45 == 45 && 45 != 45);
expect r0 == 1 <==> 45 != 45 && 45 != 45 && 45 != 45;
}
method {:test} Test71() {
var r0 := CountEqualNumbers(46, 45, 45);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 46 == 45 && 45 == 45;
expect r0 == 2 <==> (46 == 45 && 45 != 45) || (46 != 45 && 45 == 45) || (46 == 45 && 45 != 45);
expect r0 == 1 <==> 46 != 45 && 45 != 45 && 46 != 45;
}
method {:test} Test72() {
var r0 := CountEqualNumbers(46, 45, 46);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 46 == 45 && 45 == 46;
expect r0 == 2 <==> (46 == 45 && 45 != 46) || (46 != 45 && 45 == 46) || (46 == 46 && 45 != 46);
expect r0 == 1 <==> 46 != 45 && 45 != 46 && 46 != 46;
}
method {:test} Test73() {
var r0 := CountEqualNumbers(46, 47, 48);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 46 == 47 && 47 == 48;
expect r0 == 2 <==> (46 == 47 && 47 != 48) || (46 != 47 && 47 == 48) || (46 == 48 && 47 != 48);
expect r0 == 1 <==> 46 != 47 && 47 != 48 && 46 != 48;
}
method {:test} Test74() {
var r0 := CountEqualNumbers(46, 46, 45);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 46 == 46 && 46 == 45;
expect r0 == 2 <==> (46 == 46 && 46 != 45) || (46 != 46 && 46 == 45) || (46 == 45 && 46 != 45);
expect r0 == 1 <==> 46 != 46 && 46 != 45 && 46 != 45;
}

// REPEAT 6 - TIME: 158.4206909 s

method {:test} Test75() {
var r0 := CountEqualNumbers(49, 49, 49);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 49 == 49 && 49 == 49;
expect r0 == 2 <==> (49 == 49 && 49 != 49) || (49 != 49 && 49 == 49) || (49 == 49 && 49 != 49);
expect r0 == 1 <==> 49 != 49 && 49 != 49 && 49 != 49;
}
method {:test} Test76() {
var r0 := CountEqualNumbers(50, 49, 49);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 50 == 49 && 49 == 49;
expect r0 == 2 <==> (50 == 49 && 49 != 49) || (50 != 49 && 49 == 49) || (50 == 49 && 49 != 49);
expect r0 == 1 <==> 50 != 49 && 49 != 49 && 50 != 49;
}
method {:test} Test77() {
var r0 := CountEqualNumbers(50, 49, 50);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 50 == 49 && 49 == 50;
expect r0 == 2 <==> (50 == 49 && 49 != 50) || (50 != 49 && 49 == 50) || (50 == 50 && 49 != 50);
expect r0 == 1 <==> 50 != 49 && 49 != 50 && 50 != 50;
}
method {:test} Test78() {
var r0 := CountEqualNumbers(50, 49, 51);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 50 == 49 && 49 == 51;
expect r0 == 2 <==> (50 == 49 && 49 != 51) || (50 != 49 && 49 == 51) || (50 == 51 && 49 != 51);
expect r0 == 1 <==> 50 != 49 && 49 != 51 && 50 != 51;
}
method {:test} Test79() {
var r0 := CountEqualNumbers(49, 49, 50);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 49 == 49 && 49 == 50;
expect r0 == 2 <==> (49 == 49 && 49 != 50) || (49 != 49 && 49 == 50) || (49 == 50 && 49 != 50);
expect r0 == 1 <==> 49 != 49 && 49 != 50 && 49 != 50;
}

// REPEAT 7 - TIME: 166.2525021 s

method {:test} Test80() {
var r0 := CountEqualNumbers(52, 52, 52);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 52 == 52 && 52 == 52;
expect r0 == 2 <==> (52 == 52 && 52 != 52) || (52 != 52 && 52 == 52) || (52 == 52 && 52 != 52);
expect r0 == 1 <==> 52 != 52 && 52 != 52 && 52 != 52;
}
method {:test} Test81() {
var r0 := CountEqualNumbers(53, 52, 52);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 53 == 52 && 52 == 52;
expect r0 == 2 <==> (53 == 52 && 52 != 52) || (53 != 52 && 52 == 52) || (53 == 52 && 52 != 52);
expect r0 == 1 <==> 53 != 52 && 52 != 52 && 53 != 52;
}
method {:test} Test82() {
var r0 := CountEqualNumbers(53, 52, 53);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 53 == 52 && 52 == 53;
expect r0 == 2 <==> (53 == 52 && 52 != 53) || (53 != 52 && 52 == 53) || (53 == 53 && 52 != 53);
expect r0 == 1 <==> 53 != 52 && 52 != 53 && 53 != 53;
}
method {:test} Test83() {
var r0 := CountEqualNumbers(53, 52, 54);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 53 == 52 && 52 == 54;
expect r0 == 2 <==> (53 == 52 && 52 != 54) || (53 != 52 && 52 == 54) || (53 == 54 && 52 != 54);
expect r0 == 1 <==> 53 != 52 && 52 != 54 && 53 != 54;
}
method {:test} Test84() {
var r0 := CountEqualNumbers(52, 52, 53);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 52 == 52 && 52 == 53;
expect r0 == 2 <==> (52 == 52 && 52 != 53) || (52 != 52 && 52 == 53) || (52 == 53 && 52 != 53);
expect r0 == 1 <==> 52 != 52 && 52 != 53 && 52 != 53;
}

// REPEAT 8 - TIME: 174.4871906 s

method {:test} Test85() {
var r0 := CountEqualNumbers(55, 55, 55);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 55 == 55 && 55 == 55;
expect r0 == 2 <==> (55 == 55 && 55 != 55) || (55 != 55 && 55 == 55) || (55 == 55 && 55 != 55);
expect r0 == 1 <==> 55 != 55 && 55 != 55 && 55 != 55;
}
method {:test} Test86() {
var r0 := CountEqualNumbers(55, 56, 56);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 55 == 56 && 56 == 56;
expect r0 == 2 <==> (55 == 56 && 56 != 56) || (55 != 56 && 56 == 56) || (55 == 56 && 56 != 56);
expect r0 == 1 <==> 55 != 56 && 56 != 56 && 55 != 56;
}
method {:test} Test87() {
var r0 := CountEqualNumbers(56, 57, 56);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 56 == 57 && 57 == 56;
expect r0 == 2 <==> (56 == 57 && 57 != 56) || (56 != 57 && 57 == 56) || (56 == 56 && 57 != 56);
expect r0 == 1 <==> 56 != 57 && 57 != 56 && 56 != 56;
}
method {:test} Test88() {
var r0 := CountEqualNumbers(56, 55, 57);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 56 == 55 && 55 == 57;
expect r0 == 2 <==> (56 == 55 && 55 != 57) || (56 != 55 && 55 == 57) || (56 == 57 && 55 != 57);
expect r0 == 1 <==> 56 != 55 && 55 != 57 && 56 != 57;
}
method {:test} Test89() {
var r0 := CountEqualNumbers(57, 57, 55);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 57 == 57 && 57 == 55;
expect r0 == 2 <==> (57 == 57 && 57 != 55) || (57 != 57 && 57 == 55) || (57 == 55 && 57 != 55);
expect r0 == 1 <==> 57 != 57 && 57 != 55 && 57 != 55;
}

// REPEAT 9 - TIME: 182.4167924 s

method {:test} Test90() {
var r0 := CountEqualNumbers(58, 58, 58);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 58 == 58 && 58 == 58;
expect r0 == 2 <==> (58 == 58 && 58 != 58) || (58 != 58 && 58 == 58) || (58 == 58 && 58 != 58);
expect r0 == 1 <==> 58 != 58 && 58 != 58 && 58 != 58;
}
method {:test} Test91() {
var r0 := CountEqualNumbers(58, 59, 59);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 58 == 59 && 59 == 59;
expect r0 == 2 <==> (58 == 59 && 59 != 59) || (58 != 59 && 59 == 59) || (58 == 59 && 59 != 59);
expect r0 == 1 <==> 58 != 59 && 59 != 59 && 58 != 59;
}
method {:test} Test92() {
var r0 := CountEqualNumbers(58, 59, 58);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 58 == 59 && 59 == 58;
expect r0 == 2 <==> (58 == 59 && 59 != 58) || (58 != 59 && 59 == 58) || (58 == 58 && 59 != 58);
expect r0 == 1 <==> 58 != 59 && 59 != 58 && 58 != 58;
}
method {:test} Test93() {
var r0 := CountEqualNumbers(58, 60, 59);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 58 == 60 && 60 == 59;
expect r0 == 2 <==> (58 == 60 && 60 != 59) || (58 != 60 && 60 == 59) || (58 == 59 && 60 != 59);
expect r0 == 1 <==> 58 != 60 && 60 != 59 && 58 != 59;
}
method {:test} Test94() {
var r0 := CountEqualNumbers(58, 58, 59);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 58 == 58 && 58 == 59;
expect r0 == 2 <==> (58 == 58 && 58 != 59) || (58 != 58 && 58 == 59) || (58 == 59 && 58 != 59);
expect r0 == 1 <==> 58 != 58 && 58 != 59 && 58 != 59;
}

// REPEAT 10 - TIME: 190.6579718 s
