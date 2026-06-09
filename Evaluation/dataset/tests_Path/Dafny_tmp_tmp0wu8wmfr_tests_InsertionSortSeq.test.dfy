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

// REPEAT 1 - TIME: 35.4761439 s

method {:test} Test1() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 2 - TIME: 70.9843458 s

method {:test} Test2() {
var seqint0 : seq<int> := [1];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 3 - TIME: 115.4778992 s

method {:test} Test3() {
var seqint0 : seq<int> := [2, 0];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 4 - TIME: 182.9550884 s

method {:test} Test4() {
var seqint0 : seq<int> := [3];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 5 - TIME: 279.353537 s

method {:test} Test5() {
var seqint0 : seq<int> := [6, 0, 4];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 6 - TIME: 358.188222 s

method {:test} Test6() {
var seqint0 : seq<int> := [0, 0, 0, 5, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 12];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 7 - TIME: 439.7008171 s

method {:test} Test7() {
var seqint0 : seq<int> := [7, 0, 0, 0, 0, 11];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 8 - TIME: 531.9683894 s

method {:test} Test8() {
var seqint0 : seq<int> := [9];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 9 - TIME: 640.5701365 s

method {:test} Test9() {
var seqint0 : seq<int> := [15, 13];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 10 - TIME: 712.6232253 s
