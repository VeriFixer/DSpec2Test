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

// REPEAT 1 - TIME: 85.8055003 s

method {:test} Test1() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 2 - TIME: 170.5962687 s

method {:test} Test2() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 1];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 3 - TIME: 313.4284124 s

method {:test} Test3() {
var seqint0 : seq<int> := [6, 0, 0, 0, 0, 0, 2, 4];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 4 - TIME: 489.078711 s

method {:test} Test4() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 7, 3, 9];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 5 - TIME: 721.1890498 s
