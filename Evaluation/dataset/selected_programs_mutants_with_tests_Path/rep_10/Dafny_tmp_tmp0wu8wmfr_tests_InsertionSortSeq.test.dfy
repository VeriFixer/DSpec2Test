
method {:test} Test9() {
var seqint0 : seq<int> := [15, 13];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 10 - TIME: 712.6232253 s