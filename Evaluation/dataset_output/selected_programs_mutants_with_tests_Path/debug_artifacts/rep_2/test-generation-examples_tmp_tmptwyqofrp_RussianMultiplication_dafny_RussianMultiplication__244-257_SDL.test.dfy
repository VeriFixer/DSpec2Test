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

method {:test} Test2() {
var r0 := RussianMultiplication.mult(1, 2438);
expect r0 == 1 * 2438;
}
method {:test} Test3() {
var r0 := RussianMultiplication.mult(-2, 2438);
expect r0 == -2 * 2438;
}

// REPEAT 2 - TIME: 7.9036253 s
