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
var r0 := RussianMultiplication.mult(-1, 0);
expect r0 == -1 * 0;
}
method {:test} Test1() {
var r0 := RussianMultiplication.mult(1142, 8098);
expect r0 == 1142 * 8098;
}

// REPEAT 1 - TIME: 2.4603883 s
