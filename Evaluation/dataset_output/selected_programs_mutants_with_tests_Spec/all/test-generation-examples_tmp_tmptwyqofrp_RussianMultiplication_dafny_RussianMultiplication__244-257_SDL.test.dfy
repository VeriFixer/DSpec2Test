// test-generation-examples_tmp_tmptwyqofrp_RussianMultiplication_dafny_RussianMultiplication.dfy


module RussianMultiplication {
  method {:testEntry} mult(n0: int, m0: int) returns (res: int)
    ensures res == n0 * m0
  {
    var n, m: int;
    res := 0;
    if n0 >= 0 {
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

// REPEAT 1 - TIME: 2.5952212 s

method {:test} Test1() {
var r0 := RussianMultiplication.mult(7720, 1);
expect r0 == 7720 * 1;
}

// REPEAT 2 - TIME: 3.5058087 s

method {:test} Test2() {
var r0 := RussianMultiplication.mult(7721, 7721);
expect r0 == 7721 * 7721;
}

// REPEAT 3 - TIME: 4.5790043 s

method {:test} Test3() {
var r0 := RussianMultiplication.mult(7722, 7722);
expect r0 == 7722 * 7722;
}

// REPEAT 4 - TIME: 5.6048421 s

method {:test} Test4() {
var r0 := RussianMultiplication.mult(7723, 7723);
expect r0 == 7723 * 7723;
}

// REPEAT 5 - TIME: 6.5801745 s

method {:test} Test5() {
var r0 := RussianMultiplication.mult(7724, 7724);
expect r0 == 7724 * 7724;
}

// REPEAT 6 - TIME: 7.3698597 s

method {:test} Test6() {
var r0 := RussianMultiplication.mult(7725, 7725);
expect r0 == 7725 * 7725;
}

// REPEAT 7 - TIME: 7.9364787 s

method {:test} Test7() {
var r0 := RussianMultiplication.mult(7726, 7726);
expect r0 == 7726 * 7726;
}

// REPEAT 8 - TIME: 8.6373311 s

method {:test} Test8() {
var r0 := RussianMultiplication.mult(7727, 7727);
expect r0 == 7727 * 7727;
}

// REPEAT 9 - TIME: 9.1921982 s

method {:test} Test9() {
var r0 := RussianMultiplication.mult(7728, 7728);
expect r0 == 7728 * 7728;
}

// REPEAT 10 - TIME: 9.8508708 s


}
