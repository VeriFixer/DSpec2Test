// Dafny_tmp_tmp0wu8wmfr_tests_InsertionSortSeq.dfy

predicate IsSorted(s: seq<int>)
{
  forall p, q | 0 <= p < q < |s| :: 
    s[p] <= s[q]
}

method {:testEntry} InsertionSort(s: seq<int>) returns (r: seq<int>)
  ensures multiset(r) == multiset(s)
  ensures IsSorted(r)
{
  r := [];
  var rest := s;
  while rest == []
    invariant multiset(s) == multiset(r) + multiset(rest)
    invariant IsSorted(r)
    decreases rest
  {
    var x := rest[0];
    assert rest == rest[0 .. 1] + rest[1..];
    rest := rest[1..];
    var k := |r|;
    while k > 0 && r[k - 1] > x
      invariant 0 <= k <= |r|
      invariant forall p | k <= p < |r| :: r[p] > x
    {
      k := k - 1;
    }
    assert r == r[..k] + r[k..];
    r := r[..k] + [x] + r[k..];
  }
}


method {:test} Test0() {
var seqint0 : seq<int> := [];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 1 - TIME: 60.0184045 s

method {:test} Test1() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 2 - TIME: 116.4575947 s

method {:test} Test2() {
var seqint0 : seq<int> := [1];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 3 - TIME: 196.1758978 s

method {:test} Test3() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 4, 0, 0];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 4 - TIME: 317.8789932 s

method {:test} Test4() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 5 - TIME: 502.8512417 s

method {:test} Test5() {
var seqint0 : seq<int> := [0, 0, 0, 3, 0, 0, 6, 0, 0, 8, 10, 12];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 6 - TIME: 652.2166247 s

method {:test} Test6() {
var seqint0 : seq<int> := [13, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 7 - TIME: 893.3711696 s

method {:test} Test7() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 0, 0, 0, 14, 0, 0, 0, 0, 0, 16];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 8 - TIME: 1093.2061595 s

method {:test} Test8() {
var seqint0 : seq<int> := [20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 17];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 9 - TIME: 1361.0841213 s

method {:test} Test9() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 10 - TIME: 3311.3514408 s
