// dafny-synthesis_task_id_58.dfy

method {:testEntry} HasOppositeSign(a: int, b: int) returns (result: bool)
  ensures result <==> (a < 0 && b > 0) || (a > 0 && b < 0)
{
  result := (a < 0 <==> b > 0) || (a > 0 && b < 0);
}


method {:test} Test0() {
var r0 := HasOppositeSign(-1, 1);
expect r0 <==> (-1 < 0 && 1 > 0) || (-1 > 0 && 1 < 0);
}
method {:test} Test1() {
var r0 := HasOppositeSign(-100, 1);
expect r0 <==> (-100 < 0 && 1 > 0) || (-100 > 0 && 1 < 0);
}
method {:test} Test4() {
var r0 := HasOppositeSign(-1, 100);
expect r0 <==> (-1 < 0 && 100 > 0) || (-1 > 0 && 100 < 0);
}
method {:test} Test9() {
var r0 := HasOppositeSign(1, -1);
expect r0 <==> (1 < 0 && -1 > 0) || (1 > 0 && -1 < 0);
}
method {:test} Test11() {
var r0 := HasOppositeSign(100, -1);
expect r0 <==> (100 < 0 && -1 > 0) || (100 > 0 && -1 < 0);
}
method {:test} Test12() {
var r0 := HasOppositeSign(1, -100);
expect r0 <==> (1 < 0 && -100 > 0) || (1 > 0 && -100 < 0);
}
method {:test} Test18() {
var r0 := HasOppositeSign(0, 0);
expect r0 <==> (0 < 0 && 0 > 0) || (0 > 0 && 0 < 0);
}
method {:test} Test19() {
var r0 := HasOppositeSign(0, -100);
expect r0 <==> (0 < 0 && -100 > 0) || (0 > 0 && -100 < 0);
}
method {:test} Test20() {
var r0 := HasOppositeSign(0, 100);
expect r0 <==> (0 < 0 && 100 > 0) || (0 > 0 && 100 < 0);
}
method {:test} Test25() {
var r0 := HasOppositeSign(1, 0);
expect r0 <==> (1 < 0 && 0 > 0) || (1 > 0 && 0 < 0);
}
method {:test} Test26() {
var r0 := HasOppositeSign(100, 0);
expect r0 <==> (100 < 0 && 0 > 0) || (100 > 0 && 0 < 0);
}
method {:test} Test28() {
var r0 := HasOppositeSign(1, 100);
expect r0 <==> (1 < 0 && 100 > 0) || (1 > 0 && 100 < 0);
}
method {:test} Test33() {
var r0 := HasOppositeSign(-1, 0);
expect r0 <==> (-1 < 0 && 0 > 0) || (-1 > 0 && 0 < 0);
}
method {:test} Test34() {
var r0 := HasOppositeSign(-100, 0);
expect r0 <==> (-100 < 0 && 0 > 0) || (-100 > 0 && 0 < 0);
}
method {:test} Test35() {
var r0 := HasOppositeSign(-1, -100);
expect r0 <==> (-1 < 0 && -100 > 0) || (-1 > 0 && -100 < 0);
}

// REPEAT 1 - TIME: 19.9573036 s

method {:test} Test41() {
var r0 := HasOppositeSign(-2, 101);
expect r0 <==> (-2 < 0 && 101 > 0) || (-2 > 0 && 101 < 0);
}
method {:test} Test42() {
var r0 := HasOppositeSign(101, -2);
expect r0 <==> (101 < 0 && -2 > 0) || (101 > 0 && -2 < 0);
}
method {:test} Test43() {
var r0 := HasOppositeSign(101, 101);
expect r0 <==> (101 < 0 && 101 > 0) || (101 > 0 && 101 < 0);
}
method {:test} Test44() {
var r0 := HasOppositeSign(-2, -2);
expect r0 <==> (-2 < 0 && -2 > 0) || (-2 > 0 && -2 < 0);
}

// REPEAT 2 - TIME: 22.1858844 s

method {:test} Test45() {
var r0 := HasOppositeSign(-3, 102);
expect r0 <==> (-3 < 0 && 102 > 0) || (-3 > 0 && 102 < 0);
}
method {:test} Test46() {
var r0 := HasOppositeSign(102, -3);
expect r0 <==> (102 < 0 && -3 > 0) || (102 > 0 && -3 < 0);
}
method {:test} Test47() {
var r0 := HasOppositeSign(102, 102);
expect r0 <==> (102 < 0 && 102 > 0) || (102 > 0 && 102 < 0);
}
method {:test} Test48() {
var r0 := HasOppositeSign(-3, -3);
expect r0 <==> (-3 < 0 && -3 > 0) || (-3 > 0 && -3 < 0);
}

// REPEAT 3 - TIME: 24.1289107 s

method {:test} Test49() {
var r0 := HasOppositeSign(-4, 103);
expect r0 <==> (-4 < 0 && 103 > 0) || (-4 > 0 && 103 < 0);
}
method {:test} Test50() {
var r0 := HasOppositeSign(103, -4);
expect r0 <==> (103 < 0 && -4 > 0) || (103 > 0 && -4 < 0);
}
method {:test} Test51() {
var r0 := HasOppositeSign(103, 103);
expect r0 <==> (103 < 0 && 103 > 0) || (103 > 0 && 103 < 0);
}
method {:test} Test52() {
var r0 := HasOppositeSign(-4, -4);
expect r0 <==> (-4 < 0 && -4 > 0) || (-4 > 0 && -4 < 0);
}

// REPEAT 4 - TIME: 26.0293848 s

method {:test} Test53() {
var r0 := HasOppositeSign(-5, 104);
expect r0 <==> (-5 < 0 && 104 > 0) || (-5 > 0 && 104 < 0);
}
method {:test} Test54() {
var r0 := HasOppositeSign(104, -5);
expect r0 <==> (104 < 0 && -5 > 0) || (104 > 0 && -5 < 0);
}
method {:test} Test55() {
var r0 := HasOppositeSign(104, 104);
expect r0 <==> (104 < 0 && 104 > 0) || (104 > 0 && 104 < 0);
}
method {:test} Test56() {
var r0 := HasOppositeSign(-5, -5);
expect r0 <==> (-5 < 0 && -5 > 0) || (-5 > 0 && -5 < 0);
}

// REPEAT 5 - TIME: 28.0065524 s

method {:test} Test57() {
var r0 := HasOppositeSign(-6, 105);
expect r0 <==> (-6 < 0 && 105 > 0) || (-6 > 0 && 105 < 0);
}
method {:test} Test58() {
var r0 := HasOppositeSign(105, -6);
expect r0 <==> (105 < 0 && -6 > 0) || (105 > 0 && -6 < 0);
}
method {:test} Test59() {
var r0 := HasOppositeSign(105, 105);
expect r0 <==> (105 < 0 && 105 > 0) || (105 > 0 && 105 < 0);
}
method {:test} Test60() {
var r0 := HasOppositeSign(-6, -6);
expect r0 <==> (-6 < 0 && -6 > 0) || (-6 > 0 && -6 < 0);
}

// REPEAT 6 - TIME: 30.010175 s

method {:test} Test61() {
var r0 := HasOppositeSign(-7, 106);
expect r0 <==> (-7 < 0 && 106 > 0) || (-7 > 0 && 106 < 0);
}
method {:test} Test62() {
var r0 := HasOppositeSign(106, -7);
expect r0 <==> (106 < 0 && -7 > 0) || (106 > 0 && -7 < 0);
}
method {:test} Test63() {
var r0 := HasOppositeSign(106, 106);
expect r0 <==> (106 < 0 && 106 > 0) || (106 > 0 && 106 < 0);
}
method {:test} Test64() {
var r0 := HasOppositeSign(-7, -7);
expect r0 <==> (-7 < 0 && -7 > 0) || (-7 > 0 && -7 < 0);
}

// REPEAT 7 - TIME: 32.1311231 s

method {:test} Test65() {
var r0 := HasOppositeSign(-8, 107);
expect r0 <==> (-8 < 0 && 107 > 0) || (-8 > 0 && 107 < 0);
}
method {:test} Test66() {
var r0 := HasOppositeSign(107, -8);
expect r0 <==> (107 < 0 && -8 > 0) || (107 > 0 && -8 < 0);
}
method {:test} Test67() {
var r0 := HasOppositeSign(107, 107);
expect r0 <==> (107 < 0 && 107 > 0) || (107 > 0 && 107 < 0);
}
method {:test} Test68() {
var r0 := HasOppositeSign(-8, -8);
expect r0 <==> (-8 < 0 && -8 > 0) || (-8 > 0 && -8 < 0);
}

// REPEAT 8 - TIME: 33.9921855 s

method {:test} Test69() {
var r0 := HasOppositeSign(-9, 108);
expect r0 <==> (-9 < 0 && 108 > 0) || (-9 > 0 && 108 < 0);
}
method {:test} Test70() {
var r0 := HasOppositeSign(108, -9);
expect r0 <==> (108 < 0 && -9 > 0) || (108 > 0 && -9 < 0);
}
method {:test} Test71() {
var r0 := HasOppositeSign(108, 108);
expect r0 <==> (108 < 0 && 108 > 0) || (108 > 0 && 108 < 0);
}
method {:test} Test72() {
var r0 := HasOppositeSign(-9, -9);
expect r0 <==> (-9 < 0 && -9 > 0) || (-9 > 0 && -9 < 0);
}

// REPEAT 9 - TIME: 35.7601542 s

method {:test} Test73() {
var r0 := HasOppositeSign(-10, 109);
expect r0 <==> (-10 < 0 && 109 > 0) || (-10 > 0 && 109 < 0);
}
method {:test} Test74() {
var r0 := HasOppositeSign(109, -10);
expect r0 <==> (109 < 0 && -10 > 0) || (109 > 0 && -10 < 0);
}
method {:test} Test75() {
var r0 := HasOppositeSign(109, 109);
expect r0 <==> (109 < 0 && 109 > 0) || (109 > 0 && 109 < 0);
}
method {:test} Test76() {
var r0 := HasOppositeSign(-10, -10);
expect r0 <==> (-10 < 0 && -10 > 0) || (-10 > 0 && -10 < 0);
}

// REPEAT 10 - TIME: 37.5147091 s
