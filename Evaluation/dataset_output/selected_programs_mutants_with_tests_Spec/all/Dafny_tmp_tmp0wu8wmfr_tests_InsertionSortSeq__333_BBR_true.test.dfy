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
  while true
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


// Insertion sort.
//
// Author: Snorri Agnarsson, snorri@hi.is

predicate IsSorted( s: seq<int> )
{
    forall p,q | 0<=p<q<|s| :: s[p]<=s[q]
}

method {:testEntry} InsertionSort( s: seq<int> ) returns ( r: seq<int> )
    ensures multiset(r) == multiset(s);
    ensures IsSorted(r);
{
    r := [];
    var rest := s;
    while rest != []
        decreases rest;
        invariant multiset(s) == multiset(r)+multiset(rest);
        invariant IsSorted(r);
    {
        var x := rest[0];
        assert rest == rest[0..1]+rest[1..];
        rest := rest[1..];
        var k := |r|;
        while k>0 && r[k-1]>x
            invariant 0 <= k <= |r|;
            invariant forall p | k<=p<|r| :: r[p]>x;
        {
            k := k-1;
        }
        assert r == r[..k]+r[k..];
        r := r[..k]+[x]+r[k..];
    }
}

method {:test} Test0() {
var seqint0 : seq<int> := [];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 1 - TIME: 4.9552356 s

method {:test} Test1() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 2 - TIME: 6.5045439 s

method {:test} Test2() {
var seqint0 : seq<int> := [1];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 3 - TIME: 8.2517635 s

method {:test} Test3() {
var seqint0 : seq<int> := [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 4 - TIME: 9.9502 s

method {:test} Test4() {
var seqint0 : seq<int> := [6, 3];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 5 - TIME: 11.5043572 s

method {:test} Test5() {
var seqint0 : seq<int> := [10, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 6 - TIME: 12.8873808 s

method {:test} Test6() {
var seqint0 : seq<int> := [15, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 11, 0, 0, 0, 0, 13];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 7 - TIME: 14.080654 s

method {:test} Test7() {
var seqint0 : seq<int> := [14, 9, 0];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 8 - TIME: 15.4852016 s

method {:test} Test8() {
var seqint0 : seq<int> := [21, 12, 17, 19];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 9 - TIME: 16.6903537 s

method {:test} Test9() {
var seqint0 : seq<int> := [25, 20, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 23];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 10 - TIME: 17.9783445 s
