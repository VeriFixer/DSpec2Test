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
      n, m := n0, -m0;
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
var r0 := RussianMultiplication.mult(-1, 0);
expect r0 == -1 * 0;
}
method {:test} Test1() {
var r0 := RussianMultiplication.mult(1142, 8098);
expect r0 == 1142 * 8098;
}

// REPEAT 1 - TIME: 2.543326 s

method {:test} Test2() {
var r0 := RussianMultiplication.mult(-2, 32396);
expect r0 == -2 * 32396;
}
method {:test} Test3() {
var r0 := RussianMultiplication.mult(280, 16198);
expect r0 == 280 * 16198;
}

// REPEAT 2 - TIME: 3.4921955 s

method {:test} Test4() {
var r0 := RussianMultiplication.mult(-3, 32397);
expect r0 == -3 * 32397;
}
method {:test} Test5() {
var r0 := RussianMultiplication.mult(26, 32397);
expect r0 == 26 * 32397;
}

// REPEAT 3 - TIME: 4.3475521 s

method {:test} Test6() {
var r0 := RussianMultiplication.mult(-4, 32398);
expect r0 == -4 * 32398;
}
method {:test} Test7() {
var r0 := RussianMultiplication.mult(15, 32398);
expect r0 == 15 * 32398;
}

// REPEAT 4 - TIME: 4.9896622 s

method {:test} Test8() {
var r0 := RussianMultiplication.mult(-5, 32399);
expect r0 == -5 * 32399;
}
method {:test} Test9() {
var r0 := RussianMultiplication.mult(2, 32399);
expect r0 == 2 * 32399;
}

// REPEAT 5 - TIME: 5.584529 s

method {:test} Test10() {
var r0 := RussianMultiplication.mult(-6, 32400);
expect r0 == -6 * 32400;
}
method {:test} Test11() {
var r0 := RussianMultiplication.mult(1, 32400);
expect r0 == 1 * 32400;
}

// REPEAT 6 - TIME: 6.2284222 s

method {:test} Test12() {
var r0 := RussianMultiplication.mult(-7, 32401);
expect r0 == -7 * 32401;
}
method {:test} Test13() {
var r0 := RussianMultiplication.mult(0, 32401);
expect r0 == 0 * 32401;
}

// REPEAT 7 - TIME: 6.8297653 s

method {:test} Test14() {
var r0 := RussianMultiplication.mult(-8, 32402);
expect r0 == -8 * 32402;
}
method {:test} Test15() {
var r0 := RussianMultiplication.mult(3, 32402);
expect r0 == 3 * 32402;
}

// REPEAT 8 - TIME: 7.4780334 s

method {:test} Test16() {
var r0 := RussianMultiplication.mult(-9, 32403);
expect r0 == -9 * 32403;
}
method {:test} Test17() {
var r0 := RussianMultiplication.mult(1143, -1);
expect r0 == 1143 * -1;
}

// REPEAT 9 - TIME: 8.0560542 s

method {:test} Test18() {
var r0 := RussianMultiplication.mult(-10, 32404);
expect r0 == -10 * 32404;
}
method {:test} Test19() {
var r0 := RussianMultiplication.mult(1144, -2);
expect r0 == 1144 * -2;
}

// REPEAT 10 - TIME: 8.4881965 s


}
