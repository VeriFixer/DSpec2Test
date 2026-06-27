// test-generation-examples_tmp_tmptwyqofrp_RussianMultiplication_dafny_RussianMultiplication.dfy


module RussianMultiplication {
  method {:testEntry} mult(n0: int, m0: int) returns (res: int)
    ensures res == n0 * m0
  {
    var n, m: int;
    res := 0;
    if false {
      n, m := n0, m0;
    } else {
      n, m := -n0, -m0;
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
var r0 := RussianMultiplication.mult(7719, 0);
expect r0 == 7719 * 0;
}
method {:test} Test1() {
var r0 := RussianMultiplication.mult(-100, 0);
expect r0 == -100 * 0;
}
method {:test} Test2() {
var r0 := RussianMultiplication.mult(100, 0);
expect r0 == 100 * 0;
}
method {:test} Test3() {
var r0 := RussianMultiplication.mult(0, -100);
expect r0 == 0 * -100;
}
method {:test} Test4() {
var r0 := RussianMultiplication.mult(0, 100);
expect r0 == 0 * 100;
}
method {:test} Test6() {
var r0 := RussianMultiplication.mult(-100, 1);
expect r0 == -100 * 1;
}
method {:test} Test7() {
var r0 := RussianMultiplication.mult(100, 1);
expect r0 == 100 * 1;
}

// REPEAT 1 - TIME: 7.0528585 s

method {:test} Test10() {
var r0 := RussianMultiplication.mult(7720, 101);
expect r0 == 7720 * 101;
}

// REPEAT 2 - TIME: 8.1348271 s

method {:test} Test11() {
var r0 := RussianMultiplication.mult(7721, 102);
expect r0 == 7721 * 102;
}

// REPEAT 3 - TIME: 8.7693123 s

method {:test} Test12() {
var r0 := RussianMultiplication.mult(7722, 103);
expect r0 == 7722 * 103;
}

// REPEAT 4 - TIME: 9.4482202 s

method {:test} Test13() {
var r0 := RussianMultiplication.mult(7723, 104);
expect r0 == 7723 * 104;
}

// REPEAT 5 - TIME: 10.1059516 s

method {:test} Test14() {
var r0 := RussianMultiplication.mult(7724, 105);
expect r0 == 7724 * 105;
}

// REPEAT 6 - TIME: 10.7231789 s

method {:test} Test15() {
var r0 := RussianMultiplication.mult(7725, 106);
expect r0 == 7725 * 106;
}

// REPEAT 7 - TIME: 11.4092488 s

method {:test} Test16() {
var r0 := RussianMultiplication.mult(7726, 107);
expect r0 == 7726 * 107;
}

// REPEAT 8 - TIME: 11.9826757 s

method {:test} Test17() {
var r0 := RussianMultiplication.mult(7727, 108);
expect r0 == 7727 * 108;
}

// REPEAT 9 - TIME: 12.5339896 s

method {:test} Test18() {
var r0 := RussianMultiplication.mult(7728, 109);
expect r0 == 7728 * 109;
}

// REPEAT 10 - TIME: 13.1660578 s


}
