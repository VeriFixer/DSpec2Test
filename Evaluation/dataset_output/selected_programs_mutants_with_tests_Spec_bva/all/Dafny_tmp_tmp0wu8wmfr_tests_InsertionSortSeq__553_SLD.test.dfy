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
  while rest != []
    invariant multiset(s) == multiset(r) + multiset(rest)
    invariant IsSorted(r)
    decreases rest
  {
    var x := rest[0];
    assert rest == rest[0 .. 1] + rest[1..];
    rest := rest[..];
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
method {:test} Test2() {
var seqint0 : seq<int> := [0];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}
method {:test} Test3() {
var seqint0 : seq<int> := [0, 0];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 1 - TIME: 19.3645434 s

method {:test} Test10() {
var seqint0 : seq<int> := [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 2 - TIME: 21.0010989 s

method {:test} Test11() {
var seqint0 : seq<int> := [5, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 3 - TIME: 22.4779836 s

method {:test} Test12() {
var seqint0 : seq<int> := [8, 0, 4];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 4 - TIME: 23.8851097 s

method {:test} Test13() {
var seqint0 : seq<int> := [12, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 14, 10];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 5 - TIME: 25.4220427 s

method {:test} Test14() {
var seqint0 : seq<int> := [13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 6 - TIME: 27.067944 s

method {:test} Test15() {
var seqint0 : seq<int> := [18, 0, 16, 11];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 7 - TIME: 29.0328885 s

method {:test} Test16() {
var seqint0 : seq<int> := [15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 8 - TIME: 30.7979601 s

method {:test} Test17() {
var seqint0 : seq<int> := [20, 0, 0, 17, 22];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 9 - TIME: 32.2031956 s

method {:test} Test18() {
var seqint0 : seq<int> := [25, 0, 19, 23];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 10 - TIME: 33.7120391 s
