/**
  (a) Verify whether or not the following program
      satisfies total correctness.
      You should use weakest precondition reasoning
      and may extend the loop invariant if required.
      You will need to add a decreases clause to prove termination
  (a) Weakest precondition proof (without termination) (6 marks)
      Termination proof (2marks)
*/

function fusc(n: int): nat

lemma rule1()
  ensures fusc(0) == 0

lemma rule2()
  ensures fusc(1) == 1

lemma rule3(n:nat)
  ensures fusc(2*n) == fusc(n)

lemma rule4(n:nat)
  ensures fusc(2*n+1) == fusc(n) + fusc(n+1)


method {:testEntry} ComputeFusc(N: int) returns (b: int)
  requires N >= 0 
  ensures b == fusc(N)
{
  b := 0;
  var n, a := N, 1;
  assert 0 <= n <= N;
  assert fusc(N) == a * fusc(n) + b * fusc(n + 1);

  while (n != 0)
    invariant 0 <= n <= N // J
    invariant fusc(N) == a * fusc(n) + b * fusc(n + 1) // J
    decreases n // D
  {
    ghost var d := n; // termination metric

    assert fusc(N) == a * fusc(n) + b * fusc(n + 1);

    assert n != 0;

    assert (n % 2 != 0 && n % 2 == 0) || fusc(N) == a * fusc(n) + b * fusc(n + 1);
    assert (n % 2 != 0 || n % 2 == 0) ==> fusc(N) == a * fusc(n) + b * fusc(n + 1);

    assert n % 2 != 0 || fusc(N) == a * fusc(n) + b * fusc(n + 1);
    assert n % 2 == 0 || fusc(N) == a * fusc(n) + b * fusc(n + 1);
    
    assert n % 2 == 0 ==> fusc(N) == a * fusc(n) + b * fusc(n + 1);
    assert n % 2 != 0 ==> fusc(N) == a * fusc(n) + b * fusc(n + 1);

    if (n % 2 == 0)
    {
      rule4(n/2);
      assert fusc((n/2) + 1) == fusc(n + 1) - fusc(n/2);
      
      rule3(n/2);
      assert fusc(n/2) == fusc(n);
      
      assert fusc(N) == (a + b) * fusc(n/2) + b * fusc((n/2) + 1);
      
      a := a + b;
      
      assert fusc(N) == a * fusc(n/2) + b * fusc((n/2) + 1);
      
      n := n / 2;
      
      assert fusc(N) == a * fusc(n) + b * fusc(n + 1);
    } else {
      rule4((n-1)/2);
      assert fusc(n) - fusc((n-1)/2) == fusc(((n-1)/2)+1);
      
      rule3((n-1)/2);
      assert fusc((n-1)/2) == fusc(n-1);

      assert fusc(((n-1)/2)+1) == fusc((n+1)/2);
      
      rule3((n+1)/2);
      assert fusc((n+1)/2) == fusc(n+1);

      assert fusc(N) == a * fusc(n) + b * fusc(n + 1);

      assert fusc(N) == b * fusc(((n-1)/2)+1) + a * fusc(n);

      assert fusc(N) ==
              b * fusc(n) - b  * fusc(n) + b  * fusc(((n-1)/2)+1) + a * fusc(n);
      
      assert fusc(N) ==
              b * fusc(n) - b  * (fusc(n) - fusc(((n-1)/2)+1)) + a * fusc(n);
      
      assert fusc(N) == b * fusc(n) - b  * fusc((n-1)/2) + a * fusc(n);
      
      assert fusc(N) == b * fusc(n) - b  * fusc(n-1) + a * fusc(n);
      
      assert fusc(N) == b * fusc(n) - b  * fusc(n-1) + a * fusc(n);
      
      assert fusc(N) ==
              a * fusc(n - 1) + b  * fusc(n) - b  * fusc(n-1) + a * fusc(n) - a * fusc(n-1);
      assert fusc(N) == a * fusc(n - 1) + (b + a) * (fusc(n) - fusc(n-1));
 
      assert fusc(N) == a * fusc((n - 1)) + (b + a) * (fusc(n) - fusc((n-1)/2));

      assert fusc(N) == a * fusc((n - 1) / 2) + (b + a) * fusc(((n - 1) / 2) + 1);
      
      b := b + a;
      
      assert fusc(N) == a * fusc((n - 1) / 2) + b * fusc(((n - 1) / 2) + 1);
      
      n := (n - 1) / 2;

      assert fusc(N) == a * fusc(n) + b * fusc(n + 1);
    }
    assert n < d; // termination metric
    assert fusc(N) == a * fusc(n) + b * fusc(n + 1);  // J
  }
  assert n == 0; // !B

  rule1();
  assert fusc(0) == 0;

  rule2();
  assert fusc(1) == 1;

  assert fusc(N) == a * fusc(0) + b * fusc(0 + 1);  // J

  assert fusc(N) == a * 0 + b * 1; // J
  assert b == fusc(N);
}

method {:test} Test0() {
expect 2282 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFusc(2282);
expect r0 == fusc(2282);
}
method {:test} Test1() {
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFusc(1);
expect r0 == fusc(1);
}
method {:test} Test2() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFusc(2);
expect r0 == fusc(2);
}

// REPEAT 1 - TIME: 4.04448 s

method {:test} Test3() {
expect 2283 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFusc(2283);
expect r0 == fusc(2283);
}

// REPEAT 2 - TIME: 5.9172043 s

method {:test} Test6() {
expect 2284 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFusc(2284);
expect r0 == fusc(2284);
}

// REPEAT 3 - TIME: 7.740046 s

method {:test} Test9() {
expect 2285 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFusc(2285);
expect r0 == fusc(2285);
}

// REPEAT 4 - TIME: 9.4045086 s

method {:test} Test12() {
expect 2286 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFusc(2286);
expect r0 == fusc(2286);
}

// REPEAT 5 - TIME: 11.2824255 s

method {:test} Test15() {
expect 2287 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFusc(2287);
expect r0 == fusc(2287);
}

// REPEAT 6 - TIME: 12.9365964 s

method {:test} Test18() {
expect 2288 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFusc(2288);
expect r0 == fusc(2288);
}

// REPEAT 7 - TIME: 14.3726055 s

method {:test} Test21() {
expect 2289 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFusc(2289);
expect r0 == fusc(2289);
}

// REPEAT 8 - TIME: 15.4879876 s

method {:test} Test24() {
expect 2290 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFusc(2290);
expect r0 == fusc(2290);
}

// REPEAT 9 - TIME: 16.752559 s

method {:test} Test27() {
expect 2291 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFusc(2291);
expect r0 == fusc(2291);
}

// REPEAT 10 - TIME: 18.0284579 s
