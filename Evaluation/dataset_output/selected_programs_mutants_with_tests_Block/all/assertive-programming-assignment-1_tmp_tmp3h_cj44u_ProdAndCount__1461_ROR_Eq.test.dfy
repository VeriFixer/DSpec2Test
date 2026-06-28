// assertive-programming-assignment-1_tmp_tmp3h_cj44u_ProdAndCount.dfy

method {:testEntry} Main()
{
  var q := [7, -2, 3, -2];
  var p, c := ProdAndCount(q, -2);
  print "The product of all positive elements in [7,-2,3,-2] is ";
  print p;
  assert p == RecursivePositiveProduct(q) == 21;
  print "\nThe number of occurrences of -2 in [7,-2,3,-2] is ";
  print c;
  assert c == RecursiveCount(-2, q) == 2 by {
    calc {
      RecursiveCount(-2, q);
    ==
      {
        assert q[3] == -2;
        AppendOne(q, 3);
      }
      1 + RecursiveCount(-2, q[..3]);
    ==
      {
        assert q[2] != -2;
        AppendOne(q, 2);
      }
      1 + RecursiveCount(-2, q[..2]);
    ==
      {
        assert q[1] == -2;
        AppendOne(q, 1);
      }
      1 + 1 + RecursiveCount(-2, q[..1]);
    ==
      {
        assert q[0] != -2;
        AppendOne(q, 0);
      }
      1 + 1 + RecursiveCount(-2, q[..0]);
    }
  }
}

lemma AppendOne<T>(q: seq<T>, n: nat)
  requires n < |q|
  ensures q[..n] + [q[n]] == q[..n + 1]
{
}

function RecursivePositiveProduct(q: seq<int>): int
  decreases |q|
{
  if q == [] then
    1
  else if q[0] <= 0 then
    RecursivePositiveProduct(q[1..])
  else
    q[0] * RecursivePositiveProduct(q[1..])
}

function RecursiveCount(key: int, q: seq<int>): int
  decreases |q|
{
  if q == [] then
    0
  else if q[|q| - 1] == key then
    1 + RecursiveCount(key, q[..|q| - 1])
  else
    RecursiveCount(key, q[..|q| - 1])
}

method {:testEntry} ProdAndCount(q: seq<int>, key: int)
    returns (prod: int, count: nat)
  ensures prod == RecursivePositiveProduct(q)
  ensures count == RecursiveCount(key, q)
{
  prod := 1;
  count := 0;
  var size := |q|;
  var i := 0;
  var curr := 0;
  while i == size
    invariant 0 <= i <= size && count == RecursiveCount(key, q[..i]) && prod == RecursivePositiveProduct(q[..i])
    decreases size - i
  {
    Lemma_Count_Inv(q, i, count, key);
    Lemma_Prod_Inv(q, i, prod);
    curr := q[i];
    if curr > 0 {
      prod := prod * curr;
    }
    if curr == key {
      count := count + 1;
    }
    i := i + 1;
  }
  Lemma_Count_Finish(q, i, count, key);
  Lemma_Prod_Finish(q, i, prod);
}

function county(elem: int, key: int): int
{
  if elem == key then
    1
  else
    0
}

function prody(elem: int): int
{
  if elem <= 0 then
    1
  else
    elem
}

lemma Lemma_Count_Inv(q: seq<int>, i: nat, count: int, key: int)
  requires 0 <= i < |q| && count == RecursiveCount(key, q[..i])
  ensures 0 <= i + 1 <= |q| && county(q[i], key) + count == RecursiveCount(key, q[..i + 1])
{
  assert q[..i + 1] == q[..i] + [q[i]];
  var q1 := q[..i + 1];
  calc {
    RecursiveCount(key, q[..i + 1]);
  ==
    if q1 == [] then 0 else if q1[i] == key then 1 + RecursiveCount(key, q1[..i]) else RecursiveCount(key, q1[..i]);
  ==
    {
      assert q1 != [];
    }
    if q1[i] == key then 1 + RecursiveCount(key, q1[..i]) else RecursiveCount(key, q1[..i]);
  ==
    {
      KibutzLaw1(q1, key, i);
    }
    (if q1[i] == key then 1 else 0) + RecursiveCount(key, q1[..i]);
  ==
    county(q1[i], key) + RecursiveCount(key, q1[..i]);
  ==
    county(q[i], key) + RecursiveCount(key, q[..i]);
  }
}

lemma Lemma_Prod_Inv(q: seq<int>, i: nat, prod: int)
  requires 0 <= i < |q| && prod == RecursivePositiveProduct(q[..i])
  ensures 0 <= i + 1 <= |q| && prody(q[i]) * prod == RecursivePositiveProduct(q[..i + 1])
{
  assert q[..i + 1] == q[..i] + [q[i]];
  var q1 := q[..i + 1];
  calc {
    RecursivePositiveProduct(q[..i + 1]);
  ==
    if q1 == [] then 1 else if q1[0] <= 0 then RecursivePositiveProduct(q1[1..]) else q1[0] * RecursivePositiveProduct(q1[1..]);
  ==
    {
      assert q1 != [];
    }
    if q1[0] <= 0 then RecursivePositiveProduct(q1[1..]) else q1[0] * RecursivePositiveProduct(q1[1..]);
  ==
    if q[0] <= 0 then RecursivePositiveProduct(q[1 .. i + 1]) else q[0] * RecursivePositiveProduct(q[1 .. i + 1]);
  ==
    {
      KibutzLaw2(q);
    }
    (if q[0] <= 0 then 1 else q[0]) * RecursivePositiveProduct(q[1 .. i + 1]);
  ==
    prody(q[0]) * RecursivePositiveProduct(q[1 .. i + 1]);
  ==
    {
      PrependProd(q);
    }
    RecursivePositiveProduct(q[..i + 1]);
  ==
    {
      AppendProd(q[..i + 1]);
    }
    prody(q[i]) * RecursivePositiveProduct(q[..i]);
  ==
    prody(q[i]) * prod;
  }
}

lemma Lemma_Count_Finish(q: seq<int>, i: nat, count: int, key: int)
  requires inv: 0 <= i <= |q| && count == RecursiveCount(key, q[..i])
  requires neg_of_guard: i >= |q|
  ensures count == RecursiveCount(key, q)
{
  assert i <= |q| && count == RecursiveCount(key, q[..i]) by {
    reveal inv;
  }
  assert i == |q| by {
    reveal inv, neg_of_guard;
  }
  assert q[..i] == q[..|q|] == q;
}

lemma Lemma_Prod_Finish(q: seq<int>, i: nat, prod: int)
  requires inv: 0 <= i <= |q| && prod == RecursivePositiveProduct(q[..i])
  requires neg_of_guard: i >= |q|
  ensures prod == RecursivePositiveProduct(q)
{
  assert i <= |q| && prod == RecursivePositiveProduct(q[..i]) by {
    reveal inv;
  }
  assert i == |q| by {
    reveal inv, neg_of_guard;
  }
  assert q[..i] == q[..|q|] == q;
}

lemma KibutzLaw1(q: seq<int>, key: int, i: nat)
  requires q != [] && i < |q|
  ensures (if q[|q| - 1] == key then 1 + RecursiveCount(key, q[1 .. i + 1]) else 0 + RecursiveCount(key, q[1 .. i + 1])) == (if q[|q| - 1] == key then 1 else 0) + RecursiveCount(key, q[1 .. i + 1])
{
  if q[|q| - 1] == key {
    calc {
      if q[|q| - 1] == key then 1 + RecursiveCount(key, q[1 .. i + 1]) else 0 + RecursiveCount(key, q[1 .. i + 1]);
    ==
      1 + RecursiveCount(key, q[1 .. i + 1]);
    ==
      (if q[|q| - 1] == key then 1 else 0) + RecursiveCount(key, q[1 .. i + 1]);
    }
  } else {
    calc {
      if q[|q| - 1] == key then 1 + RecursiveCount(key, q[1 .. i + 1]) else 0 + RecursiveCount(key, q[1 .. i + 1]);
    ==
      0 + RecursiveCount(key, q[1 .. i + 1]);
    ==
      (if q[|q| - 1] == key then 1 else 0) + RecursiveCount(key, q[1 .. i + 1]);
    }
  }
}

lemma {:verify true} KibutzLaw2(q: seq<int>)
  requires q != []
  ensures (if q[0] <= 0 then RecursivePositiveProduct(q[1..]) else q[0] * RecursivePositiveProduct(q[1..])) == (if q[0] <= 0 then 1 else q[0]) * RecursivePositiveProduct(q[1..])
{
  if q[0] <= 0 {
    calc {
      if q[0] <= 0 then RecursivePositiveProduct(q[1..]) else q[0] * RecursivePositiveProduct(q[1..]);
    ==
      RecursivePositiveProduct(q[1..]);
    ==
      (if q[0] <= 0 then 1 else q[0]) * RecursivePositiveProduct(q[1..]);
    }
  } else {
    calc {
      if q[0] <= 0 then RecursivePositiveProduct(q[1..]) else q[0] * RecursivePositiveProduct(q[1..]);
    ==
      q[0] * RecursivePositiveProduct(q[1..]);
    ==
      (if q[0] <= 0 then 1 else q[0]) * RecursivePositiveProduct(q[1..]);
    }
  }
}

lemma AppendCount(key: int, q: seq<int>)
  requires q != []
  ensures RecursiveCount(key, q) == RecursiveCount(key, q[..|q| - 1]) + county(q[|q| - 1], key)
{
  if |q| == 1 {
    assert RecursiveCount(key, q[..|q| - 1]) + county(q[|q| - 1], key) == RecursiveCount(key, q[..0]) + county(q[0], key) == RecursiveCount(key, []) + county(q[0], key) == 0 + county(q[0], key) == county(q[0], key);
    assert RecursiveCount(key, q) == county(q[0], key);
  } else {
    var q1 := q[1..];
    calc {
      RecursiveCount(key, q);
    ==
      if q == [] then 0 else if q[|q| - 1] == key then 1 + RecursiveCount(key, q[..|q| - 1]) else RecursiveCount(key, q[..|q| - 1]);
    ==
      RecursiveCount(key, q[..|q| - 1]) + county(q[|q| - 1], key);
    }
  }
}

lemma PrependProd(q: seq<int>)
  requires q != []
  ensures RecursivePositiveProduct(q) == prody(q[0]) * RecursivePositiveProduct(q[1..])
{
  calc {
    RecursivePositiveProduct(q);
  ==
    if q == [] then 1 else if q[0] <= 0 then RecursivePositiveProduct(q[1..]) else q[0] * RecursivePositiveProduct(q[1..]);
  ==
    {
      assert q != [];
    }
    if q[0] <= 0 then RecursivePositiveProduct(q[1..]) else q[0] * RecursivePositiveProduct(q[1..]);
  ==
    {
      KibutzLaw2(q);
    }
    (if q[0] <= 0 then 1 else q[0]) * RecursivePositiveProduct(q[1..]);
  ==
    prody(q[0]) * RecursivePositiveProduct(q[1..]);
  }
}

lemma AppendProd(q: seq<int>)
  requires q != []
  ensures RecursivePositiveProduct(q) == RecursivePositiveProduct(q[..|q| - 1]) * prody(q[|q| - 1])
{
  if |q| == 1 {
    assert RecursivePositiveProduct(q[..|q| - 1]) * prody(q[|q| - 1]) == RecursivePositiveProduct(q[..0]) * prody(q[0]) == RecursivePositiveProduct([]) * prody(q[0]) == 1 * prody(q[0]) == prody(q[0]);
    assert RecursivePositiveProduct(q) == prody(q[0]);
  } else {
    var q1 := q[1..];
    calc {
      RecursivePositiveProduct(q);
    ==
      prody(q[0]) * RecursivePositiveProduct(q[1..]);
    ==
      {
        assert q1 != [];
        assert |q1| < |q|;
        AppendProd(q1);
      }
      prody(q[0]) * RecursivePositiveProduct(q1[..|q1| - 1]) * prody(q1[|q1| - 1]);
    ==
      {
        assert q1[..|q1| - 1] == q[1 .. |q| - 1];
        assert q1[|q1| - 1] == q[|q| - 1];
      }
      prody(q[0]) * RecursivePositiveProduct(q[1 .. |q| - 1]) * prody(q[|q| - 1]);
    ==
      {
        PrependProd(q[..|q| - 1]);
      }
      RecursivePositiveProduct(q[..|q| - 1]) * prody(q[|q| - 1]);
    }
  }
}


method {:test} Test0() {
Main();
}
method {:test} Test2() {
var seqint0 : seq<int> := [5921];
var r0, r1 := ProdAndCount(seqint0, 29);
expect r0 == RecursivePositiveProduct(seqint0);
expect r1 == RecursiveCount(29, seqint0);
}
method {:test} Test3() {
var seqint0 : seq<int> := [1, 0];
var r0, r1 := ProdAndCount(seqint0, 0);
expect r0 == RecursivePositiveProduct(seqint0);
expect r1 == RecursiveCount(0, seqint0);
}
method {:test} Test4() {
var seqint0 : seq<int> := [1, 4097, 5599];
var r0, r1 := ProdAndCount(seqint0, 25);
expect r0 == RecursivePositiveProduct(seqint0);
expect r1 == RecursiveCount(25, seqint0);
}
method {:test} Test5() {
var seqint0 : seq<int> := [8856, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
AppendProd(seqint0);
expect RecursivePositiveProduct(seqint0) == RecursivePositiveProduct(seqint0[..|seqint0| - 1]) * prody(seqint0[|seqint0| - 1]);
}
method {:test} Test6() {
var seqint0 : seq<int> := [2998];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
AppendProd(seqint0);
expect RecursivePositiveProduct(seqint0) == RecursivePositiveProduct(seqint0[..|seqint0| - 1]) * prody(seqint0[|seqint0| - 1]);
}

// REPEAT 1 - TIME: 39.8333064 s

method {:test} Test7() {
var seqint0 : seq<int> := [6879, 7887, 46];
var r0, r1 := ProdAndCount(seqint0, 23);
expect r0 == RecursivePositiveProduct(seqint0);
expect r1 == RecursiveCount(23, seqint0);
}
method {:test} Test8() {
var seqint0 : seq<int> := [2, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5];
var r0, r1 := ProdAndCount(seqint0, -1);
expect r0 == RecursivePositiveProduct(seqint0);
expect r1 == RecursiveCount(-1, seqint0);
}
method {:test} Test9() {
var seqint0 : seq<int> := [2, 1, 0];
var r0, r1 := ProdAndCount(seqint0, 23);
expect r0 == RecursivePositiveProduct(seqint0);
expect r1 == RecursiveCount(23, seqint0);
}
method {:test} Test10() {
var seqint0 : seq<int> := [8857, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
AppendProd(seqint0);
expect RecursivePositiveProduct(seqint0) == RecursivePositiveProduct(seqint0[..|seqint0| - 1]) * prody(seqint0[|seqint0| - 1]);
}
method {:test} Test11() {
var seqint0 : seq<int> := [1324];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
AppendProd(seqint0);
expect RecursivePositiveProduct(seqint0) == RecursivePositiveProduct(seqint0[..|seqint0| - 1]) * prody(seqint0[|seqint0| - 1]);
}

// REPEAT 2 - TIME: 43.5038219 s

method {:test} Test12() {
var seqint0 : seq<int> := [1, 1, 7, 0, 0, 0, 0, 0, 0, 9, 0, 11, 101, 75];
var r0, r1 := ProdAndCount(seqint0, 30);
expect r0 == RecursivePositiveProduct(seqint0);
expect r1 == RecursiveCount(30, seqint0);
}
method {:test} Test13() {
var seqint0 : seq<int> := [7887, -2];
var r0, r1 := ProdAndCount(seqint0, -2);
expect r0 == RecursivePositiveProduct(seqint0);
expect r1 == RecursiveCount(-2, seqint0);
}
method {:test} Test14() {
var seqint0 : seq<int> := [3, 6529, 4458];
var r0, r1 := ProdAndCount(seqint0, 30);
expect r0 == RecursivePositiveProduct(seqint0);
expect r1 == RecursiveCount(30, seqint0);
}
method {:test} Test15() {
var seqint0 : seq<int> := [2241, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
AppendProd(seqint0);
expect RecursivePositiveProduct(seqint0) == RecursivePositiveProduct(seqint0[..|seqint0| - 1]) * prody(seqint0[|seqint0| - 1]);
}
method {:test} Test16() {
var seqint0 : seq<int> := [591];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
AppendProd(seqint0);
expect RecursivePositiveProduct(seqint0) == RecursivePositiveProduct(seqint0[..|seqint0| - 1]) * prody(seqint0[|seqint0| - 1]);
}

// REPEAT 3 - TIME: 47.5119066 s

method {:test} Test17() {
var seqint0 : seq<int> := [1, 5921, 0, 0, 0, 0, 0, 0, 0, 116, 36];
var r0, r1 := ProdAndCount(seqint0, 32);
expect r0 == RecursivePositiveProduct(seqint0);
expect r1 == RecursiveCount(32, seqint0);
}
method {:test} Test18() {
var seqint0 : seq<int> := [5600, 4097, -3, 0];
var r0, r1 := ProdAndCount(seqint0, -3);
expect r0 == RecursivePositiveProduct(seqint0);
expect r1 == RecursiveCount(-3, seqint0);
}
method {:test} Test19() {
var seqint0 : seq<int> := [3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0, r1 := ProdAndCount(seqint0, 31);
expect r0 == RecursivePositiveProduct(seqint0);
expect r1 == RecursiveCount(31, seqint0);
}
method {:test} Test20() {
var seqint0 : seq<int> := [1, 0, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
AppendProd(seqint0);
expect RecursivePositiveProduct(seqint0) == RecursivePositiveProduct(seqint0[..|seqint0| - 1]) * prody(seqint0[|seqint0| - 1]);
}
method {:test} Test21() {
var seqint0 : seq<int> := [2456];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
AppendProd(seqint0);
expect RecursivePositiveProduct(seqint0) == RecursivePositiveProduct(seqint0[..|seqint0| - 1]) * prody(seqint0[|seqint0| - 1]);
}

// REPEAT 4 - TIME: 51.2778618 s

method {:test} Test22() {
var seqint0 : seq<int> := [3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 164, 138];
var r0, r1 := ProdAndCount(seqint0, 34);
expect r0 == RecursivePositiveProduct(seqint0);
expect r1 == RecursiveCount(34, seqint0);
}
method {:test} Test23() {
var seqint0 : seq<int> := [1, 16, 45, 33, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0, r1 := ProdAndCount(seqint0, 33);
expect r0 == RecursivePositiveProduct(seqint0);
expect r1 == RecursiveCount(33, seqint0);
}
method {:test} Test24() {
var seqint0 : seq<int> := [6704, 0, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
AppendProd(seqint0);
expect RecursivePositiveProduct(seqint0) == RecursivePositiveProduct(seqint0[..|seqint0| - 1]) * prody(seqint0[|seqint0| - 1]);
}
method {:test} Test25() {
var seqint0 : seq<int> := [3503];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
AppendProd(seqint0);
expect RecursivePositiveProduct(seqint0) == RecursivePositiveProduct(seqint0[..|seqint0| - 1]) * prody(seqint0[|seqint0| - 1]);
}

// REPEAT 5 - TIME: 55.1985241 s

method {:test} Test26() {
var seqint0 : seq<int> := [1, 4815, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 209, 170];
var r0, r1 := ProdAndCount(seqint0, 41);
expect r0 == RecursivePositiveProduct(seqint0);
expect r1 == RecursiveCount(41, seqint0);
}
method {:test} Test27() {
var seqint0 : seq<int> := [1, 2279, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0, r1 := ProdAndCount(seqint0, -4);
expect r0 == RecursivePositiveProduct(seqint0);
expect r1 == RecursiveCount(-4, seqint0);
}
method {:test} Test28() {
var seqint0 : seq<int> := [1, 40, 41, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0, r1 := ProdAndCount(seqint0, 35);
expect r0 == RecursivePositiveProduct(seqint0);
expect r1 == RecursiveCount(35, seqint0);
}
method {:test} Test29() {
var seqint0 : seq<int> := [7374, 0, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
AppendProd(seqint0);
expect RecursivePositiveProduct(seqint0) == RecursivePositiveProduct(seqint0[..|seqint0| - 1]) * prody(seqint0[|seqint0| - 1]);
}
method {:test} Test30() {
var seqint0 : seq<int> := [7855];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
AppendProd(seqint0);
expect RecursivePositiveProduct(seqint0) == RecursivePositiveProduct(seqint0[..|seqint0| - 1]) * prody(seqint0[|seqint0| - 1]);
}

// REPEAT 6 - TIME: 59.7854002 s

method {:test} Test31() {
var seqint0 : seq<int> := [2, 5599, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 273, 241];
var r0, r1 := ProdAndCount(seqint0, 43);
expect r0 == RecursivePositiveProduct(seqint0);
expect r1 == RecursiveCount(43, seqint0);
}
method {:test} Test32() {
var seqint0 : seq<int> := [1, 1, -5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0, r1 := ProdAndCount(seqint0, -5);
expect r0 == RecursivePositiveProduct(seqint0);
expect r1 == RecursiveCount(-5, seqint0);
}
method {:test} Test33() {
var seqint0 : seq<int> := [2, 1, 120, 0, 0];
var r0, r1 := ProdAndCount(seqint0, 42);
expect r0 == RecursivePositiveProduct(seqint0);
expect r1 == RecursiveCount(42, seqint0);
}
method {:test} Test34() {
var seqint0 : seq<int> := [7525, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
AppendProd(seqint0);
expect RecursivePositiveProduct(seqint0) == RecursivePositiveProduct(seqint0[..|seqint0| - 1]) * prody(seqint0[|seqint0| - 1]);
}
method {:test} Test35() {
var seqint0 : seq<int> := [4187];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
AppendProd(seqint0);
expect RecursivePositiveProduct(seqint0) == RecursivePositiveProduct(seqint0[..|seqint0| - 1]) * prody(seqint0[|seqint0| - 1]);
}

// REPEAT 7 - TIME: 65.0042871 s

method {:test} Test36() {
var seqint0 : seq<int> := [1, 6951, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 342, 295];
var r0, r1 := ProdAndCount(seqint0, 44);
expect r0 == RecursivePositiveProduct(seqint0);
expect r1 == RecursiveCount(44, seqint0);
}
method {:test} Test37() {
var seqint0 : seq<int> := [1, 1, -6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0, r1 := ProdAndCount(seqint0, -6);
expect r0 == RecursivePositiveProduct(seqint0);
expect r1 == RecursiveCount(-6, seqint0);
}
method {:test} Test38() {
var seqint0 : seq<int> := [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0, r1 := ProdAndCount(seqint0, 44);
expect r0 == RecursivePositiveProduct(seqint0);
expect r1 == RecursiveCount(44, seqint0);
}
method {:test} Test39() {
var seqint0 : seq<int> := [1, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
AppendProd(seqint0);
expect RecursivePositiveProduct(seqint0) == RecursivePositiveProduct(seqint0[..|seqint0| - 1]) * prody(seqint0[|seqint0| - 1]);
}
method {:test} Test40() {
var seqint0 : seq<int> := [8936];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
AppendProd(seqint0);
expect RecursivePositiveProduct(seqint0) == RecursivePositiveProduct(seqint0[..|seqint0| - 1]) * prody(seqint0[|seqint0| - 1]);
}

// REPEAT 8 - TIME: 70.7824456 s

method {:test} Test41() {
var seqint0 : seq<int> := [4166, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 401, 359];
var r0, r1 := ProdAndCount(seqint0, 50);
expect r0 == RecursivePositiveProduct(seqint0);
expect r1 == RecursiveCount(50, seqint0);
}
method {:test} Test42() {
var seqint0 : seq<int> := [1, 46, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0, r1 := ProdAndCount(seqint0, 46);
expect r0 == RecursivePositiveProduct(seqint0);
expect r1 == RecursiveCount(46, seqint0);
}
method {:test} Test43() {
var seqint0 : seq<int> := [1247];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
AppendProd(seqint0);
expect RecursivePositiveProduct(seqint0) == RecursivePositiveProduct(seqint0[..|seqint0| - 1]) * prody(seqint0[|seqint0| - 1]);
}

// REPEAT 9 - TIME: 105.0845274 s

method {:test} Test44() {
var seqint0 : seq<int> := [1, 4458, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 441, 394];
var r0, r1 := ProdAndCount(seqint0, 48);
expect r0 == RecursivePositiveProduct(seqint0);
expect r1 == RecursiveCount(48, seqint0);
}
method {:test} Test45() {
var seqint0 : seq<int> := [38, 51, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0, r1 := ProdAndCount(seqint0, 51);
expect r0 == RecursivePositiveProduct(seqint0);
expect r1 == RecursiveCount(51, seqint0);
}
method {:test} Test46() {
var seqint0 : seq<int> := [2, 0, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
AppendProd(seqint0);
expect RecursivePositiveProduct(seqint0) == RecursivePositiveProduct(seqint0[..|seqint0| - 1]) * prody(seqint0[|seqint0| - 1]);
}

// REPEAT 10 - TIME: 140.3014701 s
