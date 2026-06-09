
method {:test} Test6() {
var seqint0 : seq<int> := [15, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 11, 0, 0, 0, 0, 13];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 7 - TIME: 13.1682875 s