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
expect 38 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFusc(38);
expect r0 == fusc(38);
}

// REPEAT 1 - TIME: 4.4170466 s

method {:test} Test1() {
expect 39 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFusc(39);
expect r0 == fusc(39);
}

// REPEAT 2 - TIME: 5.3530694 s

method {:test} Test2() {
expect 40 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFusc(40);
expect r0 == fusc(40);
}

// REPEAT 3 - TIME: 6.2598139 s

method {:test} Test3() {
expect 41 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFusc(41);
expect r0 == fusc(41);
}

// REPEAT 4 - TIME: 7.31036 s

method {:test} Test4() {
expect 42 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFusc(42);
expect r0 == fusc(42);
}

// REPEAT 5 - TIME: 8.3764352 s

method {:test} Test5() {
expect 43 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFusc(43);
expect r0 == fusc(43);
}

// REPEAT 6 - TIME: 9.2537539 s

method {:test} Test6() {
expect 44 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFusc(44);
expect r0 == fusc(44);
}

// REPEAT 7 - TIME: 10.2052429 s

method {:test} Test7() {
expect 45 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFusc(45);
expect r0 == fusc(45);
}

// REPEAT 8 - TIME: 11.3272583 s

method {:test} Test8() {
expect 46 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFusc(46);
expect r0 == fusc(46);
}

// REPEAT 9 - TIME: 12.2073751 s

method {:test} Test9() {
expect 47 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFusc(47);
expect r0 == fusc(47);
}

// REPEAT 10 - TIME: 12.965889 s
