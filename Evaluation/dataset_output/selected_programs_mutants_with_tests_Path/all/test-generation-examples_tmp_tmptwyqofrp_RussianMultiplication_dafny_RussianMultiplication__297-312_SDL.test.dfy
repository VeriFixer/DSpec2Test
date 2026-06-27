// test-generation-examples_tmp_tmptwyqofrp_RussianMultiplication_dafny_RussianMultiplication.dfy


module RussianMultiplication {
  method {:testEntry} mult(n0: int, m0: int) returns (res: int)
    ensures res == n0 * m0
  {
    var n, m: int;
    res := 0;
    if n0 >= 0 {
      n, m := n0, m0;
    } else {
    }
    while 0 < n
      invariant m * n + res == m0 * n0
      decreases n
    {
      res := res + m;
      n := n - 1;
    }
  }

  export
    provides mult

}


method {:test} Test0() {
var r0 := RussianMultiplication.mult(0, 2437);
expect r0 == 0 * 2437;
}
method {:test} Test1() {
var r0 := RussianMultiplication.mult(-1, -449);
expect r0 == -1 * -449;
}

// REPEAT 1 - TIME: 4.7505919 s

method {:test} Test2() {
var r0 := RussianMultiplication.mult(1, 2438);
expect r0 == 1 * 2438;
}
method {:test} Test3() {
var r0 := RussianMultiplication.mult(-2, 2438);
expect r0 == -2 * 2438;
}

// REPEAT 2 - TIME: 7.9036253 s

method {:test} Test4() {
var r0 := RussianMultiplication.mult(2, 2439);
expect r0 == 2 * 2439;
}
method {:test} Test5() {
var r0 := RussianMultiplication.mult(-3, 2439);
expect r0 == -3 * 2439;
}

// REPEAT 3 - TIME: 10.852264 s

method {:test} Test6() {
var r0 := RussianMultiplication.mult(3, 2440);
expect r0 == 3 * 2440;
}
method {:test} Test7() {
var r0 := RussianMultiplication.mult(-4, 2440);
expect r0 == -4 * 2440;
}

// REPEAT 4 - TIME: 13.4659846 s

method {:test} Test8() {
var r0 := RussianMultiplication.mult(4, 2441);
expect r0 == 4 * 2441;
}
method {:test} Test9() {
var r0 := RussianMultiplication.mult(-5, 2441);
expect r0 == -5 * 2441;
}

// REPEAT 5 - TIME: 16.387792 s

method {:test} Test10() {
var r0 := RussianMultiplication.mult(5, 2442);
expect r0 == 5 * 2442;
}
method {:test} Test11() {
var r0 := RussianMultiplication.mult(-6, 2442);
expect r0 == -6 * 2442;
}

// REPEAT 6 - TIME: 19.7982289 s

method {:test} Test12() {
var r0 := RussianMultiplication.mult(6, 2443);
expect r0 == 6 * 2443;
}
method {:test} Test13() {
var r0 := RussianMultiplication.mult(-7, 2443);
expect r0 == -7 * 2443;
}

// REPEAT 7 - TIME: 23.2181641 s

method {:test} Test14() {
var r0 := RussianMultiplication.mult(7, 2444);
expect r0 == 7 * 2444;
}
method {:test} Test15() {
var r0 := RussianMultiplication.mult(-8, 2444);
expect r0 == -8 * 2444;
}

// REPEAT 8 - TIME: 26.1913329 s

method {:test} Test16() {
var r0 := RussianMultiplication.mult(8, 2445);
expect r0 == 8 * 2445;
}
method {:test} Test17() {
var r0 := RussianMultiplication.mult(-9, 2445);
expect r0 == -9 * 2445;
}

// REPEAT 9 - TIME: 28.5616522 s

method {:test} Test18() {
var r0 := RussianMultiplication.mult(9, 2446);
expect r0 == 9 * 2446;
}
method {:test} Test19() {
var r0 := RussianMultiplication.mult(-10, 2446);
expect r0 == -10 * 2446;
}

// REPEAT 10 - TIME: 31.1651807 s


}
