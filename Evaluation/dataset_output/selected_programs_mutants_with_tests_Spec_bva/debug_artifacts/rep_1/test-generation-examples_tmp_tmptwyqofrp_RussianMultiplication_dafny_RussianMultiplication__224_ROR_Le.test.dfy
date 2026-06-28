// test-generation-examples_tmp_tmptwyqofrp_RussianMultiplication_dafny_RussianMultiplication.dfy


module RussianMultiplication {
  method {:testEntry} mult(n0: int, m0: int) returns (res: int)
    ensures res == n0 * m0
  {
    var n, m: int;
    res := 0;
    if n0 <= 0 {
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

// REPEAT 1 - TIME: 9.1256169 s
