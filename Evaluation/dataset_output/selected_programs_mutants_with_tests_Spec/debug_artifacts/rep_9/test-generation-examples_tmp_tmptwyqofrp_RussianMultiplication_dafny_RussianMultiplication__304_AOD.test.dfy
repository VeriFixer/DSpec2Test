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

method {:test} Test8() {
var r0 := RussianMultiplication.mult(7727, 7727);
expect r0 == 7727 * 7727;
}

// REPEAT 9 - TIME: 9.1921982 s
